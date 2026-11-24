// AudioPro.inc — معالج صوت بدون تأخير إضافي (zero look-ahead) — C خالص، يُختبر بمعزل عن اللعبة
//
// السلسلة (لكل وحدة صوت): [أحادي] ← [بوابة ضوضاء] ← [قطع الدندنة 80Hz] ← [Bass/Mid/Treble]
//                         ← [ضاغط يوازن الأصوات] ← [ليميتر ناعم]
//
// مهم عن التأخير: كل مرحلة تعمل على العيّنة الحالية فقط (IIR + متتبّع سعة) بلا look-ahead وبلا مخزن،
// فالمعالجة تضيف ~0 ملّي ثانية. لا تضف هنا FFT أو مرشحات FIR طويلة لأنها تضيف تأخيراً.
#ifndef DS_AUDIOPRO_INC
#define DS_AUDIOPRO_INC

#include <math.h>
#include <string.h>
#include <stdint.h>

#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

// ---- المعاملات المشتركة (يكتبها المنيو، ويقرأها خيط الصوت) ----
typedef struct {
    volatile int   on;      // تشغيل المعالجة كلها
    volatile int   gen;     // يزيد عند أي تغيير → خيط الصوت يعيد حساب المعاملات
    volatile float bass;    // dB  (-12..+12)  رفّ منخفض عند 100Hz
    volatile float mid;     // dB  (-12..+12)  وضوح الصوت عند 2.8kHz
    volatile float treb;    // dB  (-12..+12)  رفّ مرتفع عند 6kHz
    volatile float comp;    // 0..1  قوة الضاغط (0 = متوقف)
    volatile float gate;    // 0 = متوقفة، وإلا العتبة بالـ dBFS (مثلاً -52)
    volatile int   hpf;     // قطع ما تحت 80Hz
    volatile int   mono;    // دمج القناتين
} DSAPParams;
static DSAPParams gAP;

// ---- مرشح Biquad (RBJ cookbook) ----
typedef struct { float b0, b1, b2, a1, a2; int on; } DSAPBQ;
typedef struct { float z1, z2; } DSAPBQS;

static void DSAPBQOff(DSAPBQ *c) { c->b0 = 1; c->b1 = c->b2 = c->a1 = c->a2 = 0; c->on = 0; }
static void DSAPBQSet(DSAPBQ *c, double b0, double b1, double b2, double a0, double a1, double a2) {
    c->b0 = (float)(b0 / a0); c->b1 = (float)(b1 / a0); c->b2 = (float)(b2 / a0);
    c->a1 = (float)(a1 / a0); c->a2 = (float)(a2 / a0); c->on = 1;
}
static void DSAPLowShelf(DSAPBQ *c, double sr, double f0, double dB) {
    if (fabs(dB) < 0.05) { DSAPBQOff(c); return; }
    double A = pow(10.0, dB / 40.0), w = 2 * M_PI * f0 / sr, cs = cos(w), sn = sin(w);
    double alpha = sn / 2.0 * sqrt(2.0), sa = 2 * sqrt(A) * alpha;   // S = 1
    DSAPBQSet(c, A * ((A + 1) - (A - 1) * cs + sa), 2 * A * ((A - 1) - (A + 1) * cs), A * ((A + 1) - (A - 1) * cs - sa),
                 (A + 1) + (A - 1) * cs + sa, -2 * ((A - 1) + (A + 1) * cs), (A + 1) + (A - 1) * cs - sa);
}
static void DSAPHighShelf(DSAPBQ *c, double sr, double f0, double dB) {
    if (fabs(dB) < 0.05) { DSAPBQOff(c); return; }
    double A = pow(10.0, dB / 40.0), w = 2 * M_PI * f0 / sr, cs = cos(w), sn = sin(w);
    double alpha = sn / 2.0 * sqrt(2.0), sa = 2 * sqrt(A) * alpha;
    DSAPBQSet(c, A * ((A + 1) + (A - 1) * cs + sa), -2 * A * ((A - 1) + (A + 1) * cs), A * ((A + 1) + (A - 1) * cs - sa),
                 (A + 1) - (A - 1) * cs + sa, 2 * ((A - 1) - (A + 1) * cs), (A + 1) - (A - 1) * cs - sa);
}
static void DSAPPeak(DSAPBQ *c, double sr, double f0, double Q, double dB) {
    if (fabs(dB) < 0.05) { DSAPBQOff(c); return; }
    double A = pow(10.0, dB / 40.0), w = 2 * M_PI * f0 / sr, cs = cos(w), alpha = sin(w) / (2 * Q);
    DSAPBQSet(c, 1 + alpha * A, -2 * cs, 1 - alpha * A, 1 + alpha / A, -2 * cs, 1 - alpha / A);
}
static void DSAPHighPass(DSAPBQ *c, double sr, double f0, double Q) {
    double w = 2 * M_PI * f0 / sr, cs = cos(w), alpha = sin(w) / (2 * Q);
    DSAPBQSet(c, (1 + cs) / 2, -(1 + cs), (1 + cs) / 2, 1 + alpha, -2 * cs, 1 - alpha);
}
static inline float DSAPBQRun(const DSAPBQ *c, DSAPBQS *s, float x) {   // Transposed Direct Form II
    float y = c->b0 * x + s->z1;
    s->z1 = c->b1 * x - c->a1 * y + s->z2;
    s->z2 = c->b2 * x - c->a2 * y;
    return y;
}

// ---- حالة وحدة صوت واحدة ----
typedef struct {
    int sr, gen;
    DSAPBQ hp, lo, mid, hi;
    DSAPBQS st[2][4];                       // [قناة][hp, lo, mid, hi]
    int mono;
    // الضاغط
    int compOn; float thr, ratio, knee, makeup, cEnv, cGain, cAtk, cRel, gAtk, gRel;
    // البوابة
    int gateOn; float gThr, gFloor, gEnv, gGain, gDet, gDetRel, gOpenC, gCloseC; int gHold, gHoldN;
} DSAPState;

static inline float DSAPCoef(double sr, double sec) { return (float)exp(-1.0 / (sec * sr)); }

// يعيد حساب كل المعاملات من gAP. لا يمسّ حالة المرشحات/المتتبعات حتى لا يحدث «طقّة» عند تحريك المنزلق.
static void DSAPUpdate(DSAPState *s, int sr) {
    s->sr = sr; s->gen = gAP.gen;
    s->mono = gAP.mono;
    if (gAP.hpf) DSAPHighPass(&s->hp, sr, 80.0, 0.707); else DSAPBQOff(&s->hp);
    DSAPLowShelf(&s->lo, sr, 100.0, gAP.bass);
    DSAPPeak(&s->mid, sr, 2800.0, 0.9, gAP.mid);
    DSAPHighShelf(&s->hi, sr, 6000.0, gAP.treb);

    float amt = gAP.comp; if (amt < 0) amt = 0; if (amt > 1) amt = 1;
    s->compOn = amt > 0.01f;
    s->thr = -12.0f - 18.0f * amt;                   // -12 .. -30 dBFS
    s->ratio = 1.0f + 5.0f * amt;                    // 1:1 .. 6:1
    s->knee = 6.0f;
    float mk = 0.4f * (-s->thr) * (1.0f - 1.0f / s->ratio);   // تعويض تلقائي معتدل
    s->makeup = mk > 9.0f ? 9.0f : mk;
    s->cAtk = DSAPCoef(sr, 0.003); s->cRel = DSAPCoef(sr, 0.150);   // متتبّع السعة
    s->gAtk = 1.0f - DSAPCoef(sr, 0.002); s->gRel = 1.0f - DSAPCoef(sr, 0.200);   // تنعيم الكسب
    if (s->cGain <= 0) s->cGain = 1.0f;

    float gt = gAP.gate;
    s->gateOn = gt < -1.0f;
    s->gThr = powf(10.0f, (gt < -1.0f ? gt : -60.0f) / 20.0f);
    s->gFloor = 0.178f;                              // -15 dB: تخفيض لطيف مو قطع كامل
    s->gDet = DSAPCoef(sr, 0.001); s->gDetRel = DSAPCoef(sr, 0.030);
    s->gOpenC = 1.0f - DSAPCoef(sr, 0.002); s->gCloseC = 1.0f - DSAPCoef(sr, 0.060);
    s->gHoldN = (int)(0.150 * sr);                   // يبقى مفتوحاً 150ms بعد آخر كلام (ما يقطع نهايات الكلمات)
    if (s->gGain <= 0) s->gGain = 1.0f;
}

static inline float DSAPLimit(float x) {   // ليميتر ناعم: يمرّر حتى 0.80 كما هو، وفوقها tanh حتى سقف 0.98
    const float T = 0.80f, C = 0.98f;
    float a = fabsf(x);
    if (a <= T) return x;
    float o = T + (C - T) * tanhf((a - T) / (C - T));
    return x < 0 ? -o : o;
}

static inline void DSAPFrame(DSAPState *s, float *pl, float *pr, int stereo) {
    float v[2]; v[0] = *pl; v[1] = stereo ? *pr : *pl;
    int chs = stereo ? 2 : 1;
    if (s->mono && stereo) { float m = 0.5f * (v[0] + v[1]); v[0] = v[1] = m; }

    if (s->gateOn) {   // بوابة: تخفض الهمس والضوضاء بين الكلمات
        float a = fabsf(v[0]); float b = fabsf(v[1]); if (b > a) a = b;
        s->gEnv = a + (a > s->gEnv ? s->gDet : s->gDetRel) * (s->gEnv - a);
        if (s->gEnv > s->gThr) s->gHold = s->gHoldN; else if (s->gHold > 0) s->gHold--;
        float tg = s->gHold > 0 ? 1.0f : s->gFloor;
        s->gGain += (tg - s->gGain) * (tg > s->gGain ? s->gOpenC : s->gCloseC);
        v[0] *= s->gGain; v[1] *= s->gGain;
    }
    for (int c = 0; c < chs; c++) {
        float x = v[c] + 1e-18f;   // يمنع الأعداد الدون-طبيعية (denormals)
        if (s->hp.on)  x = DSAPBQRun(&s->hp,  &s->st[c][0], x);
        if (s->lo.on)  x = DSAPBQRun(&s->lo,  &s->st[c][1], x);
        if (s->mid.on) x = DSAPBQRun(&s->mid, &s->st[c][2], x);
        if (s->hi.on)  x = DSAPBQRun(&s->hi,  &s->st[c][3], x);
        v[c] = x;
    }
    if (s->compOn) {   // ضاغط feed-forward، قناتان مرتبطتان (نفس الكسب للاثنتين حتى لا تنحرف الصورة الصوتية)
        float a = fabsf(v[0]); float b = fabsf(v[1]); if (b > a) a = b;
        s->cEnv = a + (a > s->cEnv ? s->cAtk : s->cRel) * (s->cEnv - a);
        float x = 20.0f * log10f(s->cEnv + 1e-9f), over = x - s->thr, gr;
        if (2.0f * over < -s->knee) gr = 0.0f;
        else if (2.0f * fabsf(over) <= s->knee) { float t = over + s->knee * 0.5f; gr = (1.0f / s->ratio - 1.0f) * t * t / (2.0f * s->knee); }
        else gr = (1.0f / s->ratio - 1.0f) * over;
        float tg = powf(10.0f, (gr + s->makeup) / 20.0f);
        s->cGain += (tg - s->cGain) * (tg < s->cGain ? s->gAtk : s->gRel);   // هجوم سريع عند الخفض، إفراج بطيء
        v[0] *= s->cGain; v[1] *= s->cGain;
    }
    *pl = DSAPLimit(v[0]);
    if (stereo) *pr = DSAPLimit(v[1]);
}

static void DSAPProcess(DSAPState *s, float *l, float *r, int n, int stereo) {
    for (int i = 0; i < n; i++) DSAPFrame(s, &l[i], &r[i], stereo);
}

#endif
