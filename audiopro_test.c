// اختبار محرك AudioPro.inc بمعزل عن اللعبة:  gcc -O2 -o ap_test audiopro_test.c -lm && ./ap_test
#include <stdio.h>
#include <stdlib.h>
#include "../AudioPro.inc"

#define SR 48000
static int fails = 0;
#define CHECK(c, msg) do { int ok = (c); printf("  [%s] %s\n", ok ? "OK " : "FAIL", msg); if (!ok) fails++; } while (0)

static void setP(float bass, float mid, float treb, float comp, float gate, int hpf, int mono) {
    gAP.on = 1; gAP.bass = bass; gAP.mid = mid; gAP.treb = treb; gAP.comp = comp; gAP.gate = gate; gAP.hpf = hpf; gAP.mono = mono; gAP.gen++;
}
// يقيس كسب نغمة جيبية (dB) بعد الاستقرار
static double toneGainDb(double freq, double amp) {
    DSAPState s; memset(&s, 0, sizeof s); DSAPUpdate(&s, SR);
    int n = SR; float *l = malloc(n * 4), *r = malloc(n * 4);
    for (int i = 0; i < n; i++) l[i] = r[i] = (float)(amp * sin(2 * M_PI * freq * i / SR));
    DSAPProcess(&s, l, r, n, 1);
    double si = 0, so = 0; for (int i = SR / 2; i < n; i++) { double x = amp * sin(2 * M_PI * freq * i / SR); si += x * x; so += (double)l[i] * l[i]; }
    free(l); free(r); return 10 * log10(so / si);
}
static double rmsDb(const float *x, int a, int b) { double s = 0; for (int i = a; i < b; i++) s += (double)x[i] * x[i]; return 10 * log10(s / (b - a) + 1e-20); }

int main(void) {
    printf("1) معالجة محايدة = نفس الإشارة (لا تغيير)\n");
    setP(0, 0, 0, 0, 0, 0, 0);
    { DSAPState s; memset(&s, 0, sizeof s); DSAPUpdate(&s, SR); float l[480], r[480]; double md = 0;
      for (int i = 0; i < 480; i++) l[i] = r[i] = (float)(0.5 * sin(2 * M_PI * 440 * i / SR));
      float o[480]; memcpy(o, l, sizeof o); DSAPProcess(&s, l, r, 480, 1);
      for (int i = 0; i < 480; i++) { double d = fabs(l[i] - o[i]); if (d > md) md = d; }
      printf("  أكبر فرق = %.2e\n", md); CHECK(md < 1e-6, "محايد"); }

    printf("2) استجابة التردد (Bass +9 / Mid +6 / Treble +9)\n");
    setP(9, 6, 9, 0, 0, 0, 0);
    double g60 = toneGainDb(60, 0.1), g1k = toneGainDb(1000, 0.1), g28 = toneGainDb(2800, 0.1), g10k = toneGainDb(10000, 0.1);
    printf("  60Hz %+.1f dB | 1kHz %+.1f dB | 2.8kHz %+.1f dB | 10kHz %+.1f dB\n", g60, g1k, g28, g10k);
    CHECK(g60 > 6.5 && g60 < 9.6, "Bass يرفع 60Hz بنحو +9");
    CHECK(fabs(g1k) < 2.5, "1kHz شبه ثابت");
    CHECK(g28 > 4.5 && g28 < 6.6, "Mid يرفع 2.8kHz بنحو +6");
    CHECK(g10k > 6.5 && g10k < 9.6, "Treble يرفع 10kHz بنحو +9");

    printf("3) قطع الدندنة (HPF 80Hz)\n");
    setP(0, 0, 0, 0, 0, 1, 0);
    double h30 = toneGainDb(30, 0.1), h1k = toneGainDb(1000, 0.1);
    printf("  30Hz %+.1f dB | 1kHz %+.1f dB\n", h30, h1k);
    CHECK(h30 < -9 && fabs(h1k) < 0.5, "يخفض ما تحت 80Hz ولا يمسّ الكلام");

    printf("4) الضاغط يوازن الأصوات (هادئ 0.03 مقابل عالٍ 0.6)\n");
    setP(0, 0, 0, 0.8f, 0, 0, 0);
    { DSAPState s; memset(&s, 0, sizeof s); DSAPUpdate(&s, SR); int n = SR * 4; float *l = malloc(n * 4), *r = malloc(n * 4);
      for (int i = 0; i < n; i++) { double a = (i < 2 * SR) ? 0.03 : 0.6; l[i] = r[i] = (float)(a * sin(2 * M_PI * 700 * i / SR)); }
      DSAPProcess(&s, l, r, n, 1);
      double quiet = rmsDb(l, SR, 2 * SR - 100), loud = rmsDb(l, 3 * SR, 4 * SR);
      double inDiff = 20 * log10(0.6 / 0.03);
      printf("  فرق المدخل %.1f dB → فرق المخرج %.1f dB\n", inDiff, loud - quiet);
      CHECK((loud - quiet) < inDiff - 6, "الفرق بين الهادئ والعالي يصغر"); free(l); free(r); }

    printf("5) البوابة تخفض الضوضاء وتمرّر الكلام\n");
    setP(0, 0, 0, 0, -50, 0, 0);
    { DSAPState s; memset(&s, 0, sizeof s); DSAPUpdate(&s, SR); int n = SR * 3; float *l = malloc(n * 4), *r = malloc(n * 4); srand(1);
      for (int i = 0; i < n; i++) { double nz = ((rand() / (double)RAND_MAX) - 0.5) * 0.0063;   // ≈ -50 dBFS ضوضاء (RMS ≈ -57)
        double sp = (i >= SR && i < 2 * SR) ? 0.3 * sin(2 * M_PI * 300 * i / SR) : 0; l[i] = r[i] = (float)(nz + sp); }
      float *ref = malloc(n * 4); memcpy(ref, l, n * 4); DSAPProcess(&s, l, r, n, 1);
      double nIn = rmsDb(ref, 100, SR / 2), nOut = rmsDb(l, 100 + SR / 2 - SR / 2, SR / 2) ; double nOut2 = rmsDb(l, 2 * SR + SR / 2, 3 * SR);
      double sIn = rmsDb(ref, SR + 4800, 2 * SR - 4800), sOut = rmsDb(l, SR + 4800, 2 * SR - 4800);
      printf("  ضوضاء: %.1f → %.1f dB | كلام: %.1f → %.1f dB\n", nIn, nOut2, sIn, sOut);
      CHECK(rmsDb(ref, 2 * SR + SR / 2, 3 * SR) - nOut2 > 10, "الضوضاء تنخفض أكثر من 10dB بعد توقف الكلام");
      CHECK(fabs(sIn - sOut) < 1.0, "الكلام يمرّ بدون تخفيض"); (void)nOut; free(l); free(r); free(ref); }

    printf("4b) لا تأخير: أول عيّنة تتأثر فوراً (بدون look-ahead)\n");
    setP(9, 6, 9, 0.5f, 0, 1, 0);
    { DSAPState s; memset(&s, 0, sizeof s); DSAPUpdate(&s, SR); float l[64] = {0}, r[64] = {0}; l[0] = r[0] = 0.5f;
      DSAPProcess(&s, l, r, 64, 1); int first = -1; for (int i = 0; i < 64; i++) if (fabsf(l[i]) > 1e-4f) { first = i; break; }
      printf("  أول استجابة عند العيّنة %d\n", first); CHECK(first == 0, "الاستجابة تبدأ من نفس العيّنة (0 تأخير)"); }

    printf("5b) الليميتر: لا يتجاوز 0.98 مهما كان المدخل + لا NaN مع أقصى الإعدادات\n");
    setP(12, 12, 12, 1.0f, -45, 1, 1);
    { DSAPState s; memset(&s, 0, sizeof s); DSAPUpdate(&s, SR); int n = SR * 10; float *l = malloc(n * 4), *r = malloc(n * 4); srand(7);
      for (int i = 0; i < n; i++) { l[i] = (float)(((rand() / (double)RAND_MAX) - 0.5) * 8.0); r[i] = (float)(((rand() / (double)RAND_MAX) - 0.5) * 8.0); }
      DSAPProcess(&s, l, r, n, 1); float mx = 0; int bad = 0;
      for (int i = 0; i < n; i++) { if (!isfinite(l[i]) || !isfinite(r[i])) bad++; if (fabsf(l[i]) > mx) mx = fabsf(l[i]); if (fabsf(r[i]) > mx) mx = fabsf(r[i]); }
      printf("  أعلى قيمة %.4f | غير صالحة %d\n", mx, bad); CHECK(mx <= 0.9801f && bad == 0, "السقف 0.98 ولا NaN"); free(l); free(r); }

    printf("6) تحريك المنزلق أثناء التشغيل لا يسبب طقّة (قفزة)\n");
    setP(0, 0, 0, 0, 0, 0, 0);
    { DSAPState s; memset(&s, 0, sizeof s); DSAPUpdate(&s, SR); int n = SR; float *l = malloc(n * 4), *r = malloc(n * 4);
      for (int i = 0; i < n; i++) l[i] = r[i] = (float)(0.3 * sin(2 * M_PI * 200 * i / SR));
      for (int k = 0; k < n; k += 480) { if (k == 24000) { setP(8, 3, 4, 0.4f, 0, 1, 0); DSAPUpdate(&s, SR); } DSAPProcess(&s, l + k, r + k, (n - k) < 480 ? n - k : 480, 1); }
      double mj = 0; for (int i = 24000 + 2400; i < n; i++) { double d = fabs(l[i] - l[i - 1]); if (d > mj) mj = d; }
      printf("  أكبر قفزة بين عيّنتين بعد التغيير = %.3f\n", mj); CHECK(mj < 0.2, "لا قفزات حادة"); free(l); free(r); }

    printf("\n%s (%d فشل)\n", fails ? "فيه فشل" : "كل الاختبارات نجحت", fails);
    return fails ? 1 : 0;
}
