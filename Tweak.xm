// Aflatoon Suite — DomainSniffer + ServerTester في مشروع واحد (dylib مستقل)
// © أفلاطون (Aflatoon / Plato) — جميع الحقوق محفوظة
//
// يجمع:
//   1) DomainSniffer: صيد النطاقات والـ IP وDNS، قواعد الاستبدال، NextDNS، الدردشة والصوت.
//   2) ServerTester: اختبار ضغط WebSocket/HTTP لسيرفرك الخاص.
//   3) AUTO TEST جديد: خيار ALL يصيد كل النطاقات/IP/DNS ويختبرها تلقائياً،
//      وخيار CHAT يصيد IP/DNS الخاصة بالدردشة والكتابة أونلاين ويختبرها تلقائياً.
//
// لا يحتاج Substrate / ElleKit: محرك الـ hook مدمج (إعادة ربط رموز Mach-O + ObjC runtime).

#import <UIKit/UIKit.h>
#import <WebKit/WebKit.h>
#include <poll.h>
#include <pthread.h>
#include <pthread/qos.h>
#import <Foundation/Foundation.h>
#import <QuartzCore/QuartzCore.h>
#import <AVFoundation/AVFoundation.h>
#import <AudioToolbox/AudioToolbox.h>
#import <CommonCrypto/CommonDigest.h>
#import <CommonCrypto/CommonHMAC.h>
#include <objc/runtime.h>
#include <objc/message.h>
#include <dlfcn.h>
#include <mach/mach.h>
#include <mach-o/dyld.h>
#include <mach-o/loader.h>
#include <mach-o/nlist.h>
#include <netdb.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <strings.h>
#include <sys/time.h>
#include <fcntl.h>
#include <errno.h>
#include <limits.h>
#include <sys/select.h>
#include <poll.h>
#include <stdatomic.h>
#include <os/lock.h>
#include <mach/mach_time.h>
#include "AudioPro.inc"   // AUDIO PRO: محرك معالجة الصوت (C خالص، مُختبَر بمعزل — انظر engine-test/audiopro_test.c)

#pragma mark - Store

@interface DSStore : NSObject
+ (instancetype)shared;
- (void)recordHost:(NSString *)host ips:(NSArray<NSString *> *)ips source:(NSString *)src failed:(BOOL)failed;
- (void)recordIP:(NSString *)ip port:(int)port source:(NSString *)src;
- (void)setProbe:(NSDictionary *)probe forValue:(NSString *)value;
- (NSArray<NSDictionary *> *)snapshot;
- (NSArray<NSURL *> *)saveAll;
- (NSString *)denylistText;
- (NSUInteger)denylistCount;
- (void)clear;
@end

// إرسال تلقائي عند اكتمال عدد من الأرقام (بديل «الاوجود») + إرسال لحقل دردشة اللعبة — مُعرَّفة لاحقاً
static NSString *DSDigitSendTitle(void);
static BOOL DSDigitSendIsOn(void);
static void DSDigitSendToggle(void);
static NSInteger DSDigitSendN(void);
static void DSDigitSendSetN(NSInteger n);
static BOOL DSQuickSendTo(id t, NSString *msg);
static id DSQuickTarget(void);

static BOOL DSIsIPString(NSString *s) {
    struct in_addr a4; struct in6_addr a6;
    return inet_pton(AF_INET, s.UTF8String, &a4) == 1 || inet_pton(AF_INET6, s.UTF8String, &a6) == 1;
}

static NSString *ASDir(void) {
    NSString *docs = NSSearchPathForDirectoriesInDomains(NSDocumentDirectory, NSUserDomainMask, YES).firstObject;
    NSString *dir = [docs stringByAppendingPathComponent:@"AflatoonSuite"];
    [[NSFileManager defaultManager] createDirectoryAtPath:dir withIntermediateDirectories:YES attributes:nil error:nil];

    // ترحيل إعدادات النسختين القديمتين (DomainSniffer / ServerTester) مرة واحدة فقط.
    static dispatch_once_t once;
    dispatch_once(&once, ^{
        NSFileManager *fm = [NSFileManager defaultManager];
        NSString *oldDS = [docs stringByAppendingPathComponent:@"DomainSniffer"];
        for (NSString *name in @[@"settings.json", @"data.json"]) {
            NSString *from = [oldDS stringByAppendingPathComponent:name];
            NSString *to = [dir stringByAppendingPathComponent:name];
            if (![fm fileExistsAtPath:to] && [fm fileExistsAtPath:from])
                [fm copyItemAtPath:from toPath:to error:nil];
        }
        NSString *oldST = [docs stringByAppendingPathComponent:@"ServerTester/settings.json"];
        NSString *newST = [dir stringByAppendingPathComponent:@"server-test.json"];
        if (![fm fileExistsAtPath:newST] && [fm fileExistsAtPath:oldST])
            [fm copyItemAtPath:oldST toPath:newST error:nil];
    });
    return dir;
}
#define DSDir() ASDir()


#pragma mark - Settings (persistent)

// أعلام سريعة تُقرأ من خيوط الشبكة بدون قفل
static volatile BOOL gHasRules = NO, gHasIPRules = NO;
static volatile BOOL gChatMode = NO;   // تحويل نطاقات وIPs الدردشة والكتابة أونلاين إلى 8.8.8.8
static volatile BOOL gForceAll = NO;   // تحويل كل النطاقات والـ IPs إلى 8.8.8.8 (لحظي)
static volatile BOOL gAutoDNS = YES;   // وضع DNS تلقائي → 8.8.8.8
static volatile int gKbNum = 0;                // أوضاع الأرقام: 0 OFF · 1 ترتيب (938 747) · 2 تدبيل (929 929 818 818) · 3 تدبيل الأخير (938 100 100)
static volatile BOOL gKbRev = NO;              // عكس الرسالة (هلو ← وله) — يعمل مع أي وضع
static volatile BOOL gKbNames = NO;            // أسماء بحرف: حرف واحد ← اسم لكل فئة مفعّلة
static volatile BOOL gKbKeep = NO;             // إبقاء الكيبورد مفتوحاً بعد الإرسال السريع
static volatile int gKbCats = 63;              // فئات الأسماء (بتات): ولد·بنت·حيوان·نبات·جماد·دولة
static inline BOOL DSKbXActive(void) { return gKbNum > 0 || gKbRev || gKbNames; }
static volatile BOOL gKbRepeat = NO;   // الكيبورد: تكرار الأرقام (135 → 135.135)
static volatile BOOL gKbSplit = NO;    // الكيبورد: تفكيك الحروف (حسين → ح س ي ن)
static volatile BOOL gKbSense = NO;    // الكيبورد: حساسية الكيبورد (يرسل عندما ترفع يدك عن الكيبورد)
static volatile NSInteger gKbSenseMode = 0;   // 0 = ذكي AUTO، 1..4 = مهلة ثابتة
static volatile NSInteger gKbMinChars = 1;    // أقل عدد أحرف قبل السماح بالإرسال
static volatile BOOL gKbHaptic = YES;         // اهتزاز خفيف عند الإرسال
static volatile BOOL gForceZegoOnly = NO;   // يمنع Agora من الانضمام لأي قناة، لإجبار اللعبة تستخدم Zego فقط (إن كان عندها مسار بديل)
#ifndef DS_HAS_NTGCALLS
#define DS_HAS_NTGCALLS 0   // يصير 1 تلقائياً من الـ Makefile لو وُجدت libs/libntgcalls.a
#endif
#define DS_NTG_LINKED (DS_HAS_NTGCALLS ? YES : NO)
static volatile BOOL gPingOn = NO;            // PING على الشاشة (شارة صغيرة عائمة)
static volatile NSInteger gPingTarget = 0;    // 0 = Cloudflare 1.1.1.1 ، 1 = Google 8.8.8.8 ، 2 = آخر سيرفر TCP اتصلت به اللعبة
static volatile uint32_t gPingGameIP = 0;     // آخر عنوان IPv4 عام اتصلت به اللعبة بـ TCP (شبكة big-endian)
static volatile uint16_t gPingGamePort = 0;
static volatile BOOL gLiveGlobal = NO;         // السرعة الحية على مخرج الصوت كله (Zego وغيره)
static volatile float gDSGain = 1.0f;          // تقوية الصوت: المعامل (1.0 = بدون)
static volatile int gQoSMode = 0;              // QoS: 0 OFF · 1 الصوت · 2 كل اللعبة
static volatile BOOL gDSAgoraGainOK = NO;      // Agora قبل adjustPlaybackSignalVolume → لا نضاعف التقوية على مساره
static BOOL gDSAgoraGainTouched = NO;
static volatile BOOL gLiveSpeedOn = NO;       // السرعة الحية: مفعّلة (يظهر المنيو الصغير الثاني)
static volatile float gLiveSpeed = 1.0f;      // 1 / 1.5 / 2 / 3 / 4
static volatile int gLiveDelay = 10;          // ثواني التجميع قبل اللحاق (بث حي)
static volatile int gLiveRestartGen = 0, gLiveLiveGen = 0;   // أوامر من المنيو إلى خيط الصوت
static volatile int gLiveMode = 0, gLiveA = 0, gLiveB = 0;  // حالة تُعرض في المنيو: 0 مباشر، 1 تجميع، 2 لحاق
#define DSGSSettingNote    @"DSGSSettingNote"       // تسريع اللعبة: تغيّر التشغيل/الإيقاف (لتحديث زر القائمة)
#define DSLiveSettingNote  @"DSLiveSettingNote"     // تغيّر تشغيل/إيقاف الخيار (لتحديث زر القائمة)

@interface DSSettings : NSObject
+ (instancetype)shared;
@property (atomic, copy) NSString *apiKey;
@property (atomic, copy) NSString *profileId;
@property (atomic) BOOL autoDNS;
@property (atomic) BOOL forceAll;
@property (atomic) BOOL chatMode;
@property (atomic) BOOL kbRepeatNums;
@property (atomic) BOOL kbSplitLetters;
@property (atomic) BOOL kbSense;
@property (atomic) NSInteger kbSenseMode;   // 0 ذكي، 1..4 ثابت
@property (atomic) NSInteger kbMinChars;    // 1..30
@property (atomic) BOOL kbHaptic;
@property (atomic) BOOL quickSendOn;
@property (atomic, copy) NSArray<NSString *> *chatKeywords;
@property (atomic) BOOL joinSoundOn;
@property (atomic) float joinSoundRate;   // 1..4
@property (atomic) BOOL voiceSpeedOn;
@property (atomic) BOOL liveSpeedOn;
@property (atomic) BOOL liveGlobal;
@property (atomic) BOOL pingOn;
@property (atomic) NSInteger pingTarget;   // 0..2
@property (atomic) BOOL forceZegoOnly;   // يمنع Agora من الانضمام لأي قناة
@property (atomic) float liveSpeed;      // 1..4
@property (atomic) NSInteger liveDelay;   // 0..1800 ثانية (حتى 30 دقيقة)
@property (atomic) float voiceSpeedMax;   // 1..4 — أقصى سرعة "لحاق" بصوت المتكلمين داخل الروم
- (NSArray<NSDictionary *> *)rules;
- (void)addRuleFrom:(NSString *)f to:(NSString *)t;
- (void)setRule:(NSUInteger)i enabled:(BOOL)on;
- (void)removeRule:(NSUInteger)i;
- (NSString *)targetFor:(NSString *)host;
- (BOOL)wasSent:(NSString *)d;
- (void)markSent:(NSString *)d;
- (void)save;
@end

@implementation DSSettings {
    NSMutableArray<NSDictionary *> *_rules;
    NSMutableSet<NSString *> *_sent;
}

+ (instancetype)shared {
    static DSSettings *s; static dispatch_once_t once;
    dispatch_once(&once, ^{ s = [DSSettings new]; });
    return s;
}

- (NSString *)path { return [DSDir() stringByAppendingPathComponent:@"settings.json"]; }

- (instancetype)init {
    if ((self = [super init])) {
        _rules = [NSMutableArray array];
        self.autoDNS = YES;   // الافتراضي: مفعّل
        self.kbSenseMode = 0; self.kbMinChars = 1; self.kbHaptic = YES;
        self.chatKeywords = @[];
        self.joinSoundRate = 1.0;
        self.voiceSpeedMax = 1.0;
        self.liveSpeed = 1.0; self.liveDelay = 10;
        _sent = [NSMutableSet set];
        NSData *d = [NSData dataWithContentsOfFile:[self path]];
        NSDictionary *j = d ? [NSJSONSerialization JSONObjectWithData:d options:0 error:nil] : nil;
        if ([j isKindOfClass:NSDictionary.class]) {
            self.apiKey = j[@"apiKey"];
            self.profileId = j[@"profileId"];
            if (j[@"autoDNS"]) self.autoDNS = [j[@"autoDNS"] boolValue];
            self.forceAll = [j[@"forceAll"] boolValue];
            self.chatMode = [j[@"chatMode"] boolValue];
            self.kbRepeatNums = [j[@"kbRepeatNums"] boolValue];
            self.kbSplitLetters = [j[@"kbSplitLetters"] boolValue];
            self.kbSense = [j[@"kbSense"] boolValue];
            if (j[@"kbSenseMode"]) self.kbSenseMode = MAX(0, MIN(4, [j[@"kbSenseMode"] integerValue]));
            if (j[@"kbMinChars"]) self.kbMinChars = MAX(1, MIN(30, [j[@"kbMinChars"] integerValue]));
            if (j[@"kbHaptic"]) self.kbHaptic = [j[@"kbHaptic"] boolValue];
            self.quickSendOn = [j[@"quickSendOn"] boolValue];
            if ([j[@"chatKeywords"] isKindOfClass:[NSArray class]]) self.chatKeywords = j[@"chatKeywords"];
            self.joinSoundOn = [j[@"joinSoundOn"] boolValue];
            if (j[@"joinSoundRate"]) self.joinSoundRate = [j[@"joinSoundRate"] floatValue];
            self.voiceSpeedOn = [j[@"voiceSpeedOn"] boolValue];
            self.liveSpeedOn = [j[@"liveSpeedOn"] boolValue];
            self.liveGlobal = [j[@"liveGlobal"] boolValue];
            self.forceZegoOnly = [j[@"forceZegoOnly"] boolValue]; gForceZegoOnly = self.forceZegoOnly;
            self.pingOn = [j[@"pingOn"] boolValue];
            if (j[@"pingTarget"]) self.pingTarget = MAX(0, MIN(2, [j[@"pingTarget"] integerValue]));
            if (j[@"liveSpeed"]) self.liveSpeed = MAX(1.0f, MIN(4.0f, [j[@"liveSpeed"] floatValue]));
            if (j[@"liveDelay"]) self.liveDelay = MAX(0, MIN(1800, [j[@"liveDelay"] integerValue]));
            if (j[@"voiceSpeedMax"]) self.voiceSpeedMax = [j[@"voiceSpeedMax"] floatValue];
            for (NSDictionary *r in j[@"rules"]) {
                if ([r[@"from"] isKindOfClass:NSString.class] && [r[@"to"] isKindOfClass:NSString.class])
                    [_rules addObject:@{ @"from": r[@"from"], @"to": r[@"to"], @"enabled": @([r[@"enabled"] boolValue]) }];
            }
            [_sent addObjectsFromArray:j[@"sent"] ?: @[]];
        }
        [self refreshFlags];
    }
    return self;
}

- (void)refreshFlags {  // داخل @synchronized(self) أو من init
    BOOL any = NO, ip = NO;
    for (NSDictionary *r in _rules) {
        if (![r[@"enabled"] boolValue]) continue;
        any = YES;
        if (DSIsIPString(r[@"from"])) ip = YES;
    }
    gHasRules = any; gHasIPRules = ip; gAutoDNS = self.autoDNS; gForceAll = self.forceAll; gChatMode = self.chatMode;
    gKbRepeat = self.kbRepeatNums; gKbSplit = self.kbSplitLetters; gKbSense = self.kbSense; gKbSenseMode = self.kbSenseMode; gKbMinChars = self.kbMinChars; gKbHaptic = self.kbHaptic;
    gPingOn = self.pingOn; gPingTarget = self.pingTarget; gLiveGlobal = self.liveGlobal; gLiveSpeedOn = self.liveSpeedOn; gLiveSpeed = self.liveSpeed; gLiveDelay = (int)self.liveDelay;
}

- (void)save {
    NSDictionary *dump;
    @synchronized (self) {
        [self refreshFlags];
        dump = @{ @"apiKey": self.apiKey ?: @"", @"profileId": self.profileId ?: @"", @"autoDNS": @(self.autoDNS), @"forceAll": @(self.forceAll), @"chatMode": @(self.chatMode), @"kbRepeatNums": @(self.kbRepeatNums), @"kbSplitLetters": @(self.kbSplitLetters), @"kbSense": @(self.kbSense), @"kbSenseMode": @(self.kbSenseMode), @"kbMinChars": @(self.kbMinChars), @"kbHaptic": @(self.kbHaptic), @"quickSendOn": @(self.quickSendOn), @"chatKeywords": self.chatKeywords ?: @[], @"joinSoundOn": @(self.joinSoundOn), @"joinSoundRate": @(self.joinSoundRate), @"voiceSpeedOn": @(self.voiceSpeedOn), @"voiceSpeedMax": @(self.voiceSpeedMax), @"liveSpeedOn": @(self.liveSpeedOn), @"liveGlobal": @(self.liveGlobal), @"forceZegoOnly": @(self.forceZegoOnly), @"pingOn": @(self.pingOn), @"pingTarget": @(self.pingTarget), @"liveSpeed": @(self.liveSpeed), @"liveDelay": @(self.liveDelay),
                  @"rules": [_rules copy], @"sent": [[_sent allObjects] sortedArrayUsingSelector:@selector(compare:)] };
    }
    NSData *d = [NSJSONSerialization dataWithJSONObject:dump options:NSJSONWritingPrettyPrinted error:nil];
    [d writeToFile:[self path] atomically:YES];
}

- (NSArray<NSDictionary *> *)rules { @synchronized (self) { return [_rules copy]; } }

- (void)addRuleFrom:(NSString *)f to:(NSString *)t {
    f = [f stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceAndNewlineCharacterSet].lowercaseString;
    t = [t stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceAndNewlineCharacterSet].lowercaseString;
    if (!f.length || !t.length) return;
    @synchronized (self) {
        for (NSUInteger i = 0; i < _rules.count; i++)   // نفس المصدر: حدّث الهدف
            if ([_rules[i][@"from"] isEqualToString:f]) { [_rules removeObjectAtIndex:i]; break; }
        [_rules addObject:@{ @"from": f, @"to": t, @"enabled": @YES }];
    }
    [self save];
}

- (void)setRule:(NSUInteger)i enabled:(BOOL)on {
    @synchronized (self) {
        if (i >= _rules.count) return;
        NSMutableDictionary *r = [_rules[i] mutableCopy]; r[@"enabled"] = @(on); _rules[i] = r;
    }
    [self save];
}

- (void)removeRule:(NSUInteger)i {
    @synchronized (self) { if (i < _rules.count) [_rules removeObjectAtIndex:i]; }
    [self save];
}

- (NSString *)targetFor:(NSString *)host {
    if (!gHasRules || host.length == 0) return nil;
    host = host.lowercaseString;
    @synchronized (self) {
        for (NSDictionary *r in _rules) {
            if (![r[@"enabled"] boolValue]) continue;
            NSString *f = r[@"from"];
            if ([f hasPrefix:@"*."]) { if ([host hasSuffix:[f substringFromIndex:1]]) return r[@"to"]; }
            else if ([host isEqualToString:f]) return r[@"to"];
        }
    }
    return nil;
}

- (BOOL)wasSent:(NSString *)d { @synchronized (self) { return [_sent containsObject:d.lowercaseString]; } }
- (void)markSent:(NSString *)d { @synchronized (self) { [_sent addObject:d.lowercaseString]; } [self save]; }
@end

#pragma mark - NextDNS API

static void DSNDRequest(NSString *method, NSString *path, NSDictionary *body,
                        void (^cb)(NSInteger code, id json, NSError *err)) {
    NSMutableURLRequest *r = [NSMutableURLRequest requestWithURL:
        [NSURL URLWithString:[@"https://api.nextdns.io" stringByAppendingString:path]]];
    r.HTTPMethod = method; r.timeoutInterval = 15;
    [r setValue:[DSSettings shared].apiKey ?: @"" forHTTPHeaderField:@"X-Api-Key"];
    if (body) {
        r.HTTPBody = [NSJSONSerialization dataWithJSONObject:body options:0 error:nil];
        [r setValue:@"application/json" forHTTPHeaderField:@"Content-Type"];
    }
    [[NSURLSession.sharedSession dataTaskWithRequest:r completionHandler:^(NSData *d, NSURLResponse *resp, NSError *e) {
        id j = d.length ? [NSJSONSerialization JSONObjectWithData:d options:0 error:nil] : nil;
        NSInteger code = [resp isKindOfClass:NSHTTPURLResponse.class] ? ((NSHTTPURLResponse *)resp).statusCode : 0;
        dispatch_async(dispatch_get_main_queue(), ^{ cb(code, j, e); });
    }] resume];
}

// يجلب Profile ID تلقائياً (أول حساب) إذا لم يُدخل يدوياً
static void DSNDEnsureProfile(void (^cb)(NSString *pid, NSString *err)) {
    DSSettings *st = [DSSettings shared];
    if (st.profileId.length) { cb(st.profileId, nil); return; }
    DSNDRequest(@"GET", @"/profiles", nil, ^(NSInteger code, id json, NSError *e) {
        NSArray *arr = [json isKindOfClass:NSDictionary.class] ? json[@"data"] : nil;
        id first = [arr isKindOfClass:NSArray.class] ? arr.firstObject : nil;
        NSString *pid = [first isKindOfClass:NSDictionary.class] ? first[@"id"] : nil;
        if (pid.length) { st.profileId = pid; [st save]; cb(pid, nil); return; }
        if (code == 401 || code == 403) cb(nil, @"مفتاح API غير صحيح");
        else cb(nil, e ? e.localizedDescription : @"تعذّر جلب Profile ID");
    });
}

static NSString *DSNDErrorText(NSInteger code, id json) {
    id errs = [json isKindOfClass:NSDictionary.class] ? json[@"errors"] : nil;
    id first = [errs isKindOfClass:NSArray.class] ? [errs firstObject] : nil;
    NSString *c = [first isKindOfClass:NSDictionary.class] ? first[@"code"] : nil;
    return c.length ? [NSString stringWithFormat:@"خطأ: %@", c] : [NSString stringWithFormat:@"فشل (%ld)", (long)code];
}

@implementation DSStore {
    dispatch_queue_t _q;
    NSMutableDictionary<NSString *, NSMutableDictionary *> *_items;
    NSMutableDictionary<NSString *, NSString *> *_ipHost;
    NSMutableSet<NSString *> *_seenIP;
    BOOL _saveScheduled;
}

+ (instancetype)shared {
    static DSStore *s; static dispatch_once_t once;
    dispatch_once(&once, ^{ s = [DSStore new]; });
    return s;
}

- (instancetype)init {
    if ((self = [super init])) {
        _q = dispatch_queue_create("ds.store", DISPATCH_QUEUE_SERIAL);
        _items = [NSMutableDictionary dictionary];
        _ipHost = [NSMutableDictionary dictionary];
        _seenIP = [NSMutableSet set];
        [self load];
    }
    return self;
}

- (NSMutableDictionary *)entryFor:(NSString *)v type:(NSString *)t {
    NSMutableDictionary *e = _items[v];
    if (!e) {
        e = [@{ @"type": t, @"count": @0, @"related": [NSMutableSet set], @"src": [NSMutableSet set],
                @"status": @"OK", @"probe": [NSMutableDictionary dictionary],
                @"first": @([[NSDate date] timeIntervalSince1970]), @"last": @0 } mutableCopy];
        _items[v] = e;
    }
    e[@"last"] = @([[NSDate date] timeIntervalSince1970]);
    return e;
}

- (void)recordHost:(NSString *)host ips:(NSArray<NSString *> *)ips source:(NSString *)src failed:(BOOL)failed {
    if (host.length == 0) return;
    host = host.lowercaseString;
    if ([host hasSuffix:@"nextdns.io"]) return;  // لا تسجّل طلبات الأداة نفسها
    if (DSIsIPString(host)) { [self recordIP:host port:0 source:src]; return; }
    dispatch_async(_q, ^{
        NSMutableDictionary *e = [self entryFor:host type:@"domain"];
        e[@"count"] = @([e[@"count"] integerValue] + 1);
        [e[@"src"] addObject:src];
        BOOL blocked = NO;
        for (NSString *ip in ips) {
            [e[@"related"] addObject:ip];
            self->_ipHost[ip] = host;
            if ([ip isEqualToString:@"0.0.0.0"] || [ip isEqualToString:@"::"]) blocked = YES;
        }
        if (blocked) e[@"status"] = @"BLOCKED";
        else if (failed && ips.count == 0) e[@"status"] = @"FAILED";
        else if (ips.count > 0) e[@"status"] = @"OK";
        [self markDirty];
    });
}

- (void)recordIP:(NSString *)ip port:(int)port source:(NSString *)src {
    if (ip.length == 0) return;
    NSString *key = [NSString stringWithFormat:@"%@:%d", ip, port];
    @synchronized (_seenIP) {
        if ([_seenIP containsObject:key]) return;
        [_seenIP addObject:key];
    }
    dispatch_async(_q, ^{
        NSMutableDictionary *e = [self entryFor:ip type:@"ip"];
        e[@"count"] = @([e[@"count"] integerValue] + 1);
        [e[@"src"] addObject:(port ? [NSString stringWithFormat:@"%@:%d", src, port] : src)];
        NSString *h = self->_ipHost[ip];
        if (h) [e[@"related"] addObject:h];
        [self markDirty];
    });
}

- (void)setProbe:(NSDictionary *)probe forValue:(NSString *)value {
    if (!value.length || ![probe isKindOfClass:NSDictionary.class]) return;
    dispatch_async(_q, ^{
        NSMutableDictionary *e = self->_items[value];
        if (!e) return;
        e[@"probe"] = [probe mutableCopy];
        [self markDirty];
    });
}

- (void)markDirty {  // يُستدعى داخل _q
    if (_saveScheduled) return;
    _saveScheduled = YES;
    dispatch_after(dispatch_time(DISPATCH_TIME_NOW, 5 * NSEC_PER_SEC), _q, ^{
        self->_saveScheduled = NO;
        [self writeJSON];
    });
}

- (NSArray *)sorted:(id)set { return [[set allObjects] sortedArrayUsingSelector:@selector(compare:)]; }

- (NSArray<NSDictionary *> *)snapshot {
    __block NSMutableArray *out = [NSMutableArray array];
    dispatch_sync(_q, ^{
        for (NSString *k in self->_items) {
            NSDictionary *e = self->_items[k];
            [out addObject:@{ @"value": k, @"type": e[@"type"], @"count": e[@"count"],
                              @"related": [self sorted:e[@"related"]], @"src": [self sorted:e[@"src"]],
                              @"status": e[@"status"], @"probe": e[@"probe"] ?: @{},
                              @"last": e[@"last"], @"first": e[@"first"] }];
        }
    });
    [out sortUsingComparator:^NSComparisonResult(NSDictionary *a, NSDictionary *b) {
        return [b[@"last"] compare:a[@"last"]];
    }];
    return out;
}

- (void)writeJSON {  // داخل _q
    NSMutableDictionary *dump = [NSMutableDictionary dictionary];
    for (NSString *k in _items) {
        NSDictionary *e = _items[k];
        dump[k] = @{ @"type": e[@"type"], @"count": e[@"count"], @"related": [self sorted:e[@"related"]],
                     @"src": [self sorted:e[@"src"]], @"status": e[@"status"], @"probe": e[@"probe"] ?: @{},
                     @"first": e[@"first"], @"last": e[@"last"] };
    }
    NSData *d = [NSJSONSerialization dataWithJSONObject:dump options:NSJSONWritingPrettyPrinted error:nil];
    [d writeToFile:[DSDir() stringByAppendingPathComponent:@"data.json"] atomically:YES];
}

- (void)load {
    NSData *d = [NSData dataWithContentsOfFile:[DSDir() stringByAppendingPathComponent:@"data.json"]];
    if (!d) return;
    NSDictionary *j = [NSJSONSerialization JSONObjectWithData:d options:0 error:nil];
    if (![j isKindOfClass:NSDictionary.class]) return;
    for (NSString *k in j) {
        NSDictionary *e = j[k];
        NSDictionary *pr = [e[@"probe"] isKindOfClass:NSDictionary.class] ? e[@"probe"] : @{};
        _items[k] = [@{ @"type": e[@"type"] ?: @"domain", @"count": e[@"count"] ?: @0,
                        @"related": [NSMutableSet setWithArray:e[@"related"] ?: @[]],
                        @"src": [NSMutableSet setWithArray:e[@"src"] ?: @[]],
                        @"status": e[@"status"] ?: @"OK", @"probe": [pr mutableCopy],
                        @"first": e[@"first"] ?: @0, @"last": e[@"last"] ?: @0 } mutableCopy];
    }
}

- (NSString *)denylistText {
    NSMutableArray *lines = [NSMutableArray array];
    for (NSDictionary *e in [self snapshot]) {
        if ([e[@"type"] isEqualToString:@"domain"] && ![e[@"status"] isEqualToString:@"BLOCKED"]) [lines addObject:e[@"value"]];
    }
    [lines sortUsingSelector:@selector(compare:)];
    return [lines componentsJoinedByString:@"\n"];
}

- (NSUInteger)denylistCount {
    NSString *t = [self denylistText];
    return t.length ? [t componentsSeparatedByString:@"\n"].count : 0;
}

- (NSArray<NSURL *> *)saveAll {
    NSArray *snap = [self snapshot];
    NSMutableArray *doms = [NSMutableArray array], *ips = [NSMutableArray array];
    for (NSDictionary *e in snap) {
        NSString *line = [NSString stringWithFormat:@"%@  [%@] x%@  %@", e[@"value"], e[@"status"], e[@"count"],
                          [e[@"related"] componentsJoinedByString:@","]];
        [([e[@"type"] isEqualToString:@"domain"] ? doms : ips) addObject:line];
    }
    [doms sortUsingSelector:@selector(compare:)]; [ips sortUsingSelector:@selector(compare:)];
    NSString *dir = DSDir();
    NSString *p1 = [dir stringByAppendingPathComponent:@"domains.txt"];
    NSString *p2 = [dir stringByAppendingPathComponent:@"ips.txt"];
    NSString *p3 = [dir stringByAppendingPathComponent:@"denylist_nextdns.txt"];
    [[doms componentsJoinedByString:@"\n"] writeToFile:p1 atomically:YES encoding:NSUTF8StringEncoding error:nil];
    [[ips componentsJoinedByString:@"\n"] writeToFile:p2 atomically:YES encoding:NSUTF8StringEncoding error:nil];
    [[self denylistText] writeToFile:p3 atomically:YES encoding:NSUTF8StringEncoding error:nil];
    dispatch_sync(_q, ^{ [self writeJSON]; });
    return @[ [NSURL fileURLWithPath:p3], [NSURL fileURLWithPath:p1], [NSURL fileURLWithPath:p2],
              [NSURL fileURLWithPath:[dir stringByAppendingPathComponent:@"data.json"]] ];
}

- (void)clear {
    dispatch_sync(_q, ^{
        [self->_items removeAllObjects]; [self->_ipHost removeAllObjects];
        [self writeJSON];
    });
    @synchronized (_seenIP) { [_seenIP removeAllObjects]; }
}
@end

#pragma mark - Network hooks

static NSString *DSAddrString(const struct sockaddr *sa) {
    char buf[INET6_ADDRSTRLEN];
    if (!sa) return nil;
    if (sa->sa_family == AF_INET) {
        if (inet_ntop(AF_INET, &((const struct sockaddr_in *)sa)->sin_addr, buf, sizeof buf)) return @(buf);
    } else if (sa->sa_family == AF_INET6) {
        if (inet_ntop(AF_INET6, &((const struct sockaddr_in6 *)sa)->sin6_addr, buf, sizeof buf)) return @(buf);
    }
    return nil;
}

static void DSNoteSockaddr(const struct sockaddr *sa, socklen_t len, const char *src) {
    if (!sa || len == 0 || len > sizeof(struct sockaddr_storage)) return;
    static __thread struct sockaddr_storage last;
    static __thread socklen_t lastLen;
    if (lastLen == len && memcmp(&last, sa, len) == 0) return;
    memcpy(&last, sa, len); lastLen = len;

    int port = 0;
    if (sa->sa_family == AF_INET) port = ntohs(((const struct sockaddr_in *)sa)->sin_port);
    else if (sa->sa_family == AF_INET6) port = ntohs(((const struct sockaddr_in6 *)sa)->sin6_port);
    else return;
    NSString *ip = DSAddrString(sa);
    if (!ip || [ip isEqualToString:@"127.0.0.1"] || [ip isEqualToString:@"::1"] || [ip isEqualToString:@"0.0.0.0"] || [ip isEqualToString:@"::"]) return;
    [[DSStore shared] recordIP:ip port:port source:@(src)];
}

// استبدال نطاق/IP في DNS حسب القواعد المفعّلة
static BOOL DSMapNode(const char *node, char *out, size_t n) {
    if (!node || !gHasRules) return NO;
    NSString *h = [NSString stringWithUTF8String:node];
    NSString *to = h ? [[DSSettings shared] targetFor:h] : nil;
    if (!to) return NO;
    strlcpy(out, to.UTF8String, n);
    return YES;
}

// ====== DNS تلقائي → 8.8.8.8 ======
#define DS_GDNS4 "8.8.8.8"
#define DS_GDNS6 "2001:4860:4860::8888"

static ssize_t (*orig_sendto)(int, const void *, size_t, int, const struct sockaddr *, socklen_t);

// أي اتصال بمنفذ 53 (UDP/TCP) إلى سيرفر DNS غير Google → يتحوّل إلى 8.8.8.8 (المنفذ نفسه)
static BOOL DSDNSRewrite(const struct sockaddr *sa, socklen_t len, struct sockaddr_storage *out) {
    if (sa->sa_family == AF_INET && len >= sizeof(struct sockaddr_in)) {
        const struct sockaddr_in *a = (const struct sockaddr_in *)sa;
        if (ntohs(a->sin_port) != 53) return NO;
        uint32_t ip = ntohl(a->sin_addr.s_addr);
        if (ip == 0 || (ip >> 24) == 127 || ip == 0x08080808) return NO;
        memcpy(out, sa, len);
        return inet_pton(AF_INET, DS_GDNS4, &((struct sockaddr_in *)out)->sin_addr) == 1;
    }
    if (sa->sa_family == AF_INET6 && len >= sizeof(struct sockaddr_in6)) {
        const struct sockaddr_in6 *a = (const struct sockaddr_in6 *)sa;
        if (ntohs(a->sin6_port) != 53) return NO;
        struct in6_addr g; if (inet_pton(AF_INET6, DS_GDNS6, &g) != 1) return NO;
        if (IN6_IS_ADDR_LOOPBACK(&a->sin6_addr) || IN6_IS_ADDR_UNSPECIFIED(&a->sin6_addr) ||
            memcmp(&a->sin6_addr, &g, sizeof g) == 0) return NO;
        memcpy(out, sa, len);
        ((struct sockaddr_in6 *)out)->sin6_addr = g;
        return YES;
    }
    return NO;
}

// ---- وضع "الكل → 8.8.8.8" ----
static NSMutableSet *DSExemptSet(void) {   // IPs سيرفرات NextDNS (كي تبقى القائمة شغّالة)
    static NSMutableSet *x; static dispatch_once_t once;
    dispatch_once(&once, ^{ x = [NSMutableSet set]; });
    return x;
}
static BOOL DSIsNextDNSHost(const char *h) {
    size_t l = h ? strlen(h) : 0;
    return l >= 10 && strcasecmp(h + l - 10, "nextdns.io") == 0;
}
static void DSExemptAdd(const struct addrinfo *list) {
    @synchronized (DSExemptSet()) {
        for (const struct addrinfo *p = list; p; p = p->ai_next) {
            NSString *a = DSAddrString(p->ai_addr);
            if (a) [DSExemptSet() addObject:a];
        }
    }
}
static BOOL DSIsLocalAddr(const struct sockaddr *sa) {
    if (sa->sa_family == AF_INET) {
        uint32_t ip = ntohl(((const struct sockaddr_in *)sa)->sin_addr.s_addr);
        return ip == 0 || (ip >> 24) == 127 || (ip >> 24) == 10 || (ip >> 16) == 0xC0A8 ||
               (ip >> 20) == 0xAC1 || (ip >> 16) == 0xA9FE;
    }
    if (sa->sa_family == AF_INET6) {
        const struct in6_addr *a = &((const struct sockaddr_in6 *)sa)->sin6_addr;
        return IN6_IS_ADDR_LOOPBACK(a) || IN6_IS_ADDR_UNSPECIFIED(a) || IN6_IS_ADDR_LINKLOCAL(a) || (a->s6_addr[0] & 0xFE) == 0xFC;
    }
    return YES;
}
// ---- وضع "الدردشة والكتابة أونلاين → 8.8.8.8" ----
static NSMutableSet *DSChatIPs(void) {   // IPs الدردشة التي تعلّمناها من حلّ أسماءها
    static NSMutableSet *x; static dispatch_once_t once;
    dispatch_once(&once, ^{ x = [NSMutableSet set]; });
    return x;
}
static NSArray *DSChatSubstrings(void) {
    static NSArray *a;
    static dispatch_once_t once;
    dispatch_once(&once, ^{ a = @[@"chat", @"typing", @"online", @"presence", @"messag", @"msgr", @"websocket", @"socket.io", @"signalr",
        @"xmpp", @"mqtt", @"agora", @"sendbird", @"pubnub", @"pusher", @"getstream", @"stream-io", @"twilio",
        @"cometchat", @"talkjs", @"livechat", @"tawk", @"zopim", @"whatsapp", @"telegram", @"discord", @"ably"]; });
    return a;
}
static NSSet *DSChatTokens(void) {
    static NSSet *a;
    static dispatch_once_t once;
    dispatch_once(&once, ^{ a = [NSSet setWithArray:@[@"im", @"dm", @"msg", @"msgs", @"rtm", @"ws", @"wss",
        @"socket", @"sockets", @"realtime", @"presence", @"comms"]]; });
    return a;
}
static BOOL DSIsChatHost(const char *h) {
    if (!h || !h[0] || DSIsNextDNSHost(h)) return NO;
    NSString *s = [@(h) lowercaseString];
    if (!s) return NO;
    for (NSString *k in DSChatSubstrings()) if ([s containsString:k]) return YES;
    NSArray *tok = [s componentsSeparatedByCharactersInSet:[NSCharacterSet characterSetWithCharactersInString:@".-_"]];
    NSSet *ex = DSChatTokens();
    for (NSString *t in tok) if ([ex containsObject:t]) return YES;
    for (NSString *k in [DSSettings shared].chatKeywords)       // كلمات إضافية من settings.json
        if ([k isKindOfClass:[NSString class]] && k.length && [s containsString:k.lowercaseString]) return YES;
    return NO;
}
static void DSChatIPAdd(const struct addrinfo *list) {
    @synchronized (DSChatIPs()) {
        for (const struct addrinfo *p = list; p; p = p->ai_next) {
            NSString *a = DSAddrString(p->ai_addr);
            if (a) [DSChatIPs() addObject:a];
        }
    }
}
static BOOL DSChatEligible(const char *node, const struct addrinfo *hints) {
    if (!node || !node[0] || !strchr(node, '.')) return NO;
    struct in_addr a4; struct in6_addr a6;
    if (inet_pton(AF_INET, node, &a4) == 1 || inet_pton(AF_INET6, node, &a6) == 1) return NO;
    if (hints) {
        if (hints->ai_family != AF_UNSPEC && hints->ai_family != AF_INET) return NO;
        if (hints->ai_flags & (AI_NUMERICHOST | AI_PASSIVE | AI_CANONNAME)) return NO;
    }
    return DSIsChatHost(node);
}
static const char *DSPortStr(const char *service, char *buf, size_t n) {   // https / wss → رقم
    if (!service) return NULL;
    if (strcasecmp(service, "https") == 0 || strcasecmp(service, "wss") == 0) return "443";
    if (strcasecmp(service, "http") == 0 || strcasecmp(service, "ws") == 0) return "80";
    strlcpy(buf, service, n); return buf;
}
static BOOL DSChatRewrite(const struct sockaddr *sa, socklen_t len, struct sockaddr_storage *out) {
    if (sa->sa_family != AF_INET && sa->sa_family != AF_INET6) return NO;
    NSString *ip = DSAddrString(sa);
    if (!ip) return NO;
    BOOL hit; @synchronized (DSChatIPs()) { hit = [DSChatIPs() containsObject:ip]; }
    if (!hit) return NO;
    memcpy(out, sa, len);
    if (sa->sa_family == AF_INET && len >= sizeof(struct sockaddr_in))
        return inet_pton(AF_INET, DS_GDNS4, &((struct sockaddr_in *)out)->sin_addr) == 1;
    if (sa->sa_family == AF_INET6 && len >= sizeof(struct sockaddr_in6))
        return inet_pton(AF_INET6, DS_GDNS6, &((struct sockaddr_in6 *)out)->sin6_addr) == 1;
    return NO;
}
static BOOL DSForceRewrite(const struct sockaddr *sa, socklen_t len, struct sockaddr_storage *out) {
    if (sa->sa_family != AF_INET && sa->sa_family != AF_INET6) return NO;
    if (DSIsLocalAddr(sa)) return NO;
    NSString *ip = DSAddrString(sa);
    if (!ip || [ip isEqualToString:@DS_GDNS4] || [ip isEqualToString:@DS_GDNS6]) return NO;
    @synchronized (DSExemptSet()) { if ([DSExemptSet() containsObject:ip]) return NO; }
    memcpy(out, sa, len);
    if (sa->sa_family == AF_INET && len >= sizeof(struct sockaddr_in))
        return inet_pton(AF_INET, DS_GDNS4, &((struct sockaddr_in *)out)->sin_addr) == 1;
    if (sa->sa_family == AF_INET6 && len >= sizeof(struct sockaddr_in6))
        return inet_pton(AF_INET6, DS_GDNS6, &((struct sockaddr_in6 *)out)->sin6_addr) == 1;
    return NO;
}

// استبدال IP في connect/sendto: قواعد المستخدم أولاً، ثم وضع DNS التلقائي
static BOOL DSRewriteSockaddr(const struct sockaddr *sa, socklen_t len, struct sockaddr_storage *out) {
    if (!sa || len == 0 || len > sizeof(*out)) return NO;
    if (gHasIPRules) {
        NSString *ip = DSAddrString(sa);
        NSString *to = ip ? [[DSSettings shared] targetFor:ip] : nil;
        if (to) {
            memcpy(out, sa, len);
            if (sa->sa_family == AF_INET) {
                struct in_addr a;
                if (inet_pton(AF_INET, to.UTF8String, &a) == 1) { ((struct sockaddr_in *)out)->sin_addr = a; return YES; }
            } else if (sa->sa_family == AF_INET6) {
                struct in6_addr a;
                if (inet_pton(AF_INET6, to.UTF8String, &a) == 1) { ((struct sockaddr_in6 *)out)->sin6_addr = a; return YES; }
            }
        }
    }
    if (gForceAll && DSForceRewrite(sa, len, out)) return YES;
    if (gChatMode && DSChatRewrite(sa, len, out)) return YES;
    if (gAutoDNS && DSDNSRewrite(sa, len, out)) return YES;
    return NO;
}

// ==== DS_RESOLVER_C_BEGIN ====
// محلّل DNS مدمج: يسأل 8.8.8.8 مباشرة (سجل A) بدل DNS الجهاز/الشبكة
static const char *gDNSServer = DS_GDNS4;
static uint16_t gDNSPort = 53;
static volatile double gDNSDownUntil = 0;   // إذا تعذّر الوصول لـ 8.8.8.8 نتجاوزه مؤقتاً

static double DSNow(void) { struct timespec ts; clock_gettime(CLOCK_REALTIME, &ts); return (double)ts.tv_sec + ts.tv_nsec / 1e9; }

static size_t DSSkipName(const uint8_t *r, size_t n, size_t i) {
    while (i < n) {
        uint8_t l = r[i];
        if (l == 0) return i + 1;
        if ((l & 0xC0) == 0xC0) return (i + 2 <= n) ? i + 2 : 0;
        if (l & 0xC0) return 0;
        i += 1 + l;
    }
    return 0;
}

static BOOL DSDNSQuery4(const char *host, struct in_addr *outs, int max, int *count, uint32_t *minTTL) {
    size_t hl = strlen(host);
    if (hl == 0 || hl > 253) return NO;
    uint8_t q[320]; size_t o = 0;
    uint16_t id = (uint16_t)arc4random();
    q[o++] = id >> 8; q[o++] = id & 0xFF; q[o++] = 0x01; q[o++] = 0x00;      // ID + RD
    q[o++] = 0; q[o++] = 1; q[o++] = 0; q[o++] = 0; q[o++] = 0; q[o++] = 0; q[o++] = 0; q[o++] = 0;
    const char *p = host;
    while (*p) {
        const char *dot = strchr(p, '.');
        size_t ll = dot ? (size_t)(dot - p) : strlen(p);
        if (ll == 0 || ll > 63 || o + ll + 6 > sizeof q) return NO;
        q[o++] = (uint8_t)ll; memcpy(q + o, p, ll); o += ll;
        p += ll; if (*p == '.') p++;
    }
    q[o++] = 0; q[o++] = 0; q[o++] = 1; q[o++] = 0; q[o++] = 1;                // A / IN

    int fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) return NO;
    struct timeval tv = { 1, 200000 };
    setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
    struct sockaddr_in dst; memset(&dst, 0, sizeof dst);
    dst.sin_len = sizeof dst; dst.sin_family = AF_INET; dst.sin_port = htons(gDNSPort);
    inet_pton(AF_INET, gDNSServer, &dst.sin_addr);

    ssize_t (*snd)(int, const void *, size_t, int, const struct sockaddr *, socklen_t) = orig_sendto ? orig_sendto : sendto;
    uint8_t r[1500]; ssize_t rn = -1;
    for (int t = 0; t < 2; t++) {
        if (snd(fd, q, o, 0, (struct sockaddr *)&dst, sizeof dst) < 0) break;
        rn = recvfrom(fd, r, sizeof r, 0, NULL, NULL);
        if (rn >= 12 && r[0] == q[0] && r[1] == q[1]) break;
        rn = -1;
    }
    close(fd);
    if (rn < 12) { gDNSDownUntil = DSNow() + 20.0; return NO; }               // لا رد: تجاوز 20 ثانية
    if (!(r[2] & 0x80) || (r[3] & 0x0F) != 0) return NO;                       // ليس رداً سليماً (NXDOMAIN وغيره)

    size_t N = (size_t)rn, i = 12;
    int qd = (r[4] << 8) | r[5], an = (r[6] << 8) | r[7];
    for (int k = 0; k < qd; k++) { i = DSSkipName(r, N, i); if (!i || i + 4 > N) return NO; i += 4; }
    int c = 0; uint32_t mt = 0xFFFFFFFFu;
    for (int k = 0; k < an && i < N; k++) {
        i = DSSkipName(r, N, i); if (!i || i + 10 > N) break;
        uint16_t type = (r[i] << 8) | r[i + 1], cls = (r[i + 2] << 8) | r[i + 3];
        uint32_t ttl = ((uint32_t)r[i + 4] << 24) | (r[i + 5] << 16) | (r[i + 6] << 8) | r[i + 7];
        uint16_t rdl = (r[i + 8] << 8) | r[i + 9];
        i += 10; if (i + rdl > N) break;
        if (type == 1 && cls == 1 && rdl == 4 && c < max) { memcpy(&outs[c++], r + i, 4); if (ttl < mt) mt = ttl; }
        i += rdl;
    }
    *count = c; *minTTL = (mt == 0xFFFFFFFFu) ? 0 : mt;
    return c > 0;
}

// يبني قائمة addrinfo (تُحرَّر بـ freeaddrinfo العادية: كل عقدة وعنوانها بـ malloc منفصل)
static struct addrinfo *DSBuildAddrInfo(const struct in_addr *ips, int n, const char *service, const struct addrinfo *hints) {
    int port = service ? atoi(service) : 0;
    int socktype = hints ? hints->ai_socktype : 0, proto = hints ? hints->ai_protocol : 0;
    int types[2], tc = 0;
    if (socktype == 0) { types[tc++] = SOCK_STREAM; types[tc++] = SOCK_DGRAM; } else types[tc++] = socktype;
    struct addrinfo *head = NULL, *tail = NULL;
    for (int i = 0; i < n; i++) for (int t = 0; t < tc; t++) {
        struct addrinfo *ai = (struct addrinfo *)calloc(1, sizeof *ai);
        struct sockaddr_in *sin = (struct sockaddr_in *)calloc(1, sizeof *sin);
        if (!ai || !sin) { free(ai); free(sin); continue; }
        sin->sin_len = sizeof *sin; sin->sin_family = AF_INET; sin->sin_port = htons((uint16_t)port); sin->sin_addr = ips[i];
        ai->ai_flags = hints ? hints->ai_flags : 0; ai->ai_family = AF_INET; ai->ai_socktype = types[t];
        ai->ai_protocol = proto ? proto : (types[t] == SOCK_STREAM ? IPPROTO_TCP : (types[t] == SOCK_DGRAM ? IPPROTO_UDP : 0));
        ai->ai_addrlen = sizeof *sin; ai->ai_addr = (struct sockaddr *)sin;
        if (tail) tail->ai_next = ai; else head = ai;
        tail = ai;
    }
    return head;
}
// ==== DS_RESOLVER_C_END ====

static NSMutableDictionary *DSDNSCache(void) {
    static NSMutableDictionary *c; static dispatch_once_t once;
    dispatch_once(&once, ^{ c = [NSMutableDictionary dictionary]; });
    return c;
}

static BOOL DSResolve4(const char *host, struct in_addr *outs, int max, int *count) {
    NSString *key = @(host).lowercaseString;
    if (!key) return NO;
    double now = DSNow();
    @synchronized (DSDNSCache()) {
        NSDictionary *e = DSDNSCache()[key];
        if (e && [e[@"exp"] doubleValue] > now) {
            NSData *d = e[@"ips"]; int n = (int)(d.length / sizeof(struct in_addr)); if (n > max) n = max;
            memcpy(outs, d.bytes, n * sizeof(struct in_addr)); *count = n; return n > 0;
        }
    }
    uint32_t ttl = 0; int n = 0;
    if (!DSDNSQuery4(host, outs, max, &n, &ttl) || n <= 0) return NO;
    if (ttl < 10) ttl = 10; if (ttl > 300) ttl = 300;
    @synchronized (DSDNSCache()) {
        if (DSDNSCache().count > 512) [DSDNSCache() removeAllObjects];
        DSDNSCache()[key] = @{ @"ips": [NSData dataWithBytes:outs length:n * sizeof(struct in_addr)], @"exp": @(now + ttl) };
    }
    *count = n; return YES;
}

// متى نستخدم المحلّل المدمج؟ فقط للأسماء العادية؛ غير ذلك نتركه للنظام
static BOOL DSNameEligible(const char *node, const char *service, const struct addrinfo *hints) {
    if (!node || !node[0]) return NO;
    if (!strchr(node, '.')) return NO;                                          // localhost وأسماء محلية
    struct in_addr a4; struct in6_addr a6;
    if (inet_pton(AF_INET, node, &a4) == 1 || inet_pton(AF_INET6, node, &a6) == 1) return NO;
    size_t l = strlen(node);
    if (l > 6 && strcasecmp(node + l - 6, ".local") == 0) return NO;
    if (hints) {
        if (hints->ai_family != AF_UNSPEC && hints->ai_family != AF_INET) return NO;
        if (hints->ai_flags & (AI_NUMERICHOST | AI_PASSIVE | AI_CANONNAME)) return NO;
    }
    if (service) { for (const char *c = service; *c; c++) if (*c < '0' || *c > '9') return NO; }
    return YES;
}
static BOOL DSShouldAutoResolve(const char *node, const char *service, const struct addrinfo *hints) {
    if (!gAutoDNS || DSNow() < gDNSDownUntil) return NO;
    return DSNameEligible(node, service, hints);
}
static BOOL DSForceEligible(const char *node, const char *service, const struct addrinfo *hints) {
    return gForceAll && DSNameEligible(node, service, hints) && !DSIsNextDNSHost(node);
}

static struct hostent *DSAutoHostent(const char *name) {
    static __thread struct hostent he; static __thread char nameBuf[256];
    static __thread struct in_addr addrs[16]; static __thread char *list[17]; static __thread char *aliases[1];
    struct in_addr ips[16]; int n = 0;
    if (!DSShouldAutoResolve(name, NULL, NULL) || !DSResolve4(name, ips, 16, &n) || n <= 0) return NULL;
    for (int i = 0; i < n; i++) { addrs[i] = ips[i]; list[i] = (char *)&addrs[i]; }
    list[n] = NULL; aliases[0] = NULL;
    strlcpy(nameBuf, name, sizeof nameBuf);
    he.h_name = nameBuf; he.h_aliases = aliases; he.h_addrtype = AF_INET; he.h_length = 4; he.h_addr_list = list;
    return &he;
}

static int (*orig_getaddrinfo)(const char *, const char *, const struct addrinfo *, struct addrinfo **);
static int hook_getaddrinfo(const char *node, const char *service, const struct addrinfo *hints, struct addrinfo **res) {
    char mapped[256];
    BOOL isMapped = DSMapNode(node, mapped, sizeof mapped);
    int r = -1; BOOL done = NO;
    if (!isMapped && res && DSForceEligible(node, service, hints)) {          // الكل → 8.8.8.8
        struct in_addr g; inet_pton(AF_INET, DS_GDNS4, &g);
        struct addrinfo *fl = DSBuildAddrInfo(&g, 1, service, hints);
        if (fl) { *res = fl; r = 0; done = YES; }
    }
    if (!done && !isMapped && res && gChatMode && DSChatEligible(node, hints)) {   // دردشة/كتابة → 8.8.8.8
        struct addrinfo *real = NULL;
        if (orig_getaddrinfo(node, service, hints, &real) == 0 && real) { DSChatIPAdd(real); freeaddrinfo(real); }
        char pb[32]; struct in_addr g; inet_pton(AF_INET, DS_GDNS4, &g);
        struct addrinfo *cl = DSBuildAddrInfo(&g, 1, DSPortStr(service, pb, sizeof pb), hints);
        if (cl) { *res = cl; r = 0; done = YES; }
    }
    if (!done && !isMapped && res && DSShouldAutoResolve(node, service, hints)) {   // DNS = 8.8.8.8
        struct in_addr ips4[16]; int cnt = 0;
        if (DSResolve4(node, ips4, 16, &cnt)) {
            struct addrinfo *list = DSBuildAddrInfo(ips4, cnt, service, hints);
            if (list) { *res = list; r = 0; done = YES; }
        }
    }
    if (!done) r = orig_getaddrinfo(isMapped ? mapped : node, service, hints, res);   // احتياطي: DNS النظام
    if (r == 0 && res && *res && DSIsNextDNSHost(node)) DSExemptAdd(*res);
    // تعلّم IPs الدردشة/الكتابة أونلاين حتى لو لم يُفعّل CHAT → 8.8.8.8،
    // ليعرف AUTO TEST (CHAT) أي IP يخص الدردشة عند اختبار الأهداف الملتقطة.
    if (r == 0 && res && *res && node && !isMapped && DSChatEligible(node, hints)) DSChatIPAdd(*res);
    if (node) {
        NSMutableArray *ips = [NSMutableArray array];
        if (r == 0 && res && *res) {
            for (struct addrinfo *p = *res; p; p = p->ai_next) {
                NSString *s = DSAddrString(p->ai_addr);
                if (s && ![ips containsObject:s]) [ips addObject:s];
            }
        }
        NSString *h = [NSString stringWithUTF8String:node];
        if (h) [[DSStore shared] recordHost:h ips:ips source:@"dns" failed:(r != 0)];
    }
    return r;
}

static struct hostent *(*orig_gethostbyname)(const char *);
static struct hostent *hook_gethostbyname(const char *name) {
    char mapped[256];
    BOOL isMapped = DSMapNode(name, mapped, sizeof mapped);
    struct hostent *r = NULL;
    if (!isMapped && DSForceEligible(name, NULL, NULL)) {                       // الكل → 8.8.8.8
        static __thread struct hostent fh; static __thread char fn[256]; static __thread struct in_addr fa;
        static __thread char *fl[2]; static __thread char *fal[1];
        inet_pton(AF_INET, DS_GDNS4, &fa); fl[0] = (char *)&fa; fl[1] = NULL; fal[0] = NULL;
        strlcpy(fn, name, sizeof fn);
        fh.h_name = fn; fh.h_aliases = fal; fh.h_addrtype = AF_INET; fh.h_length = 4; fh.h_addr_list = fl;
        r = &fh;
    }
    if (!r && !isMapped && gChatMode && DSChatEligible(name, NULL)) {            // دردشة/كتابة → 8.8.8.8
        struct hostent *real = orig_gethostbyname(name);
        if (real && real->h_addrtype == AF_INET && real->h_addr_list) {
            for (char **a = real->h_addr_list; *a; a++) {
                char b[INET_ADDRSTRLEN];
                if (inet_ntop(AF_INET, *a, b, sizeof b)) @synchronized (DSChatIPs()) { [DSChatIPs() addObject:@(b)]; }
            }
        }
        static __thread struct hostent ch; static __thread char cn[256]; static __thread struct in_addr ca;
        static __thread char *cl[2]; static __thread char *cal[1];
        inet_pton(AF_INET, DS_GDNS4, &ca); cl[0] = (char *)&ca; cl[1] = NULL; cal[0] = NULL;
        strlcpy(cn, name, sizeof cn);
        ch.h_name = cn; ch.h_aliases = cal; ch.h_addrtype = AF_INET; ch.h_length = 4; ch.h_addr_list = cl;
        r = &ch;
    }
    if (!r && !isMapped) r = DSAutoHostent(name);                   // DNS = 8.8.8.8
    if (!r) r = orig_gethostbyname(isMapped ? mapped : name);
    // تعلّم IPs الدردشة/الكتابة أونلاين مثل getaddrinfo، لتعمل CHAT تلقائياً في AUTO TEST.
    if (r && !isMapped && name && DSChatEligible(name, NULL) && r->h_addrtype == AF_INET && r->h_addr_list) {
        for (char **a = r->h_addr_list; *a; a++) {
            char b[INET_ADDRSTRLEN];
            if (inet_ntop(AF_INET, *a, b, sizeof b)) @synchronized (DSChatIPs()) { [DSChatIPs() addObject:@(b)]; }
        }
    }
    if (name) {
        NSString *h = [NSString stringWithUTF8String:name];
        if (h) [[DSStore shared] recordHost:h ips:nil source:@"dns" failed:(r == NULL)];
    }
    return r;
}

#pragma mark - Proxy engine (SOCKS5 / HTTP CONNECT)

// يمرّر اتصالات TCP الخام عبر بروكسي (SOCKS5 أو HTTP CONNECT) + يحقن البروكسي في جلسات NSURLSession.
// لا يدعم UDP ولا vmess/vless/trojan/ss (تحتاج نواة خارجية).

typedef NS_ENUM(NSInteger, DSProxyType) { DSProxyTypeSOCKS5 = 1, DSProxyTypeHTTP = 2 };
typedef struct { int type; int port; char host[256]; char user[256]; char pass[256]; } DSProxyCfg;

static volatile BOOL gProxyOn = NO;
static _Atomic int32_t gProxyHits = 0, gProxyFails = 0;

static NSString *DSB64Decode(NSString *s) {
    NSString *t = [[s stringByReplacingOccurrencesOfString:@"-" withString:@"+"] stringByReplacingOccurrencesOfString:@"_" withString:@"/"];
    while (t.length % 4) t = [t stringByAppendingString:@"="];
    NSData *d = [[NSData alloc] initWithBase64EncodedString:t options:0];
    return d ? [[NSString alloc] initWithData:d encoding:NSUTF8StringEncoding] : nil;
}

static int DSProxyGuessType(int port) {   // رابط بلا scheme: المنافذ المعروفة لـ HTTP تُعامل كـ HTTP والباقي SOCKS5
    switch (port) { case 80: case 808: case 3128: case 3129: case 8000: case 8080: case 8081: case 8118: case 8888: return DSProxyTypeHTTP; }
    return DSProxyTypeSOCKS5;
}

@interface DSProxy : NSObject
@property (atomic) BOOL enabled;
@property (atomic, copy) NSString *link;
@property (atomic) int type, port;
@property (atomic, copy) NSString *host, *user, *pass, *lastError;
+ (instancetype)shared;
- (BOOL)applyLink:(NSString *)link error:(NSString **)err;   // يحفظ + يفعّل
- (void)save;
- (BOOL)getCfg:(DSProxyCfg *)out;
- (NSString *)summary;
- (NSDictionary *)cfDict;
@end

@implementation DSProxy

+ (instancetype)shared {
    static DSProxy *p; static dispatch_once_t once;
    dispatch_once(&once, ^{ p = [DSProxy new]; });
    return p;
}

- (NSString *)path { return [DSDir() stringByAppendingPathComponent:@"proxy.json"]; }

- (instancetype)init {
    if ((self = [super init])) {
        NSData *d = [NSData dataWithContentsOfFile:[self path]];
        NSDictionary *j = d ? [NSJSONSerialization JSONObjectWithData:d options:0 error:nil] : nil;
        if ([j isKindOfClass:NSDictionary.class] && [j[@"link"] isKindOfClass:NSString.class]) {
            NSString *e = nil;
            if ([self parseLink:j[@"link"] error:&e]) { self.link = j[@"link"]; self.enabled = [j[@"enabled"] boolValue]; }
        }
        gProxyOn = self.enabled && self.host.length > 0;
    }
    return self;
}

- (void)save {
    @synchronized (self) {
        gProxyOn = self.enabled && self.host.length > 0;
        NSDictionary *j = @{ @"enabled": @(self.enabled), @"link": self.link ?: @"" };
        [[NSJSONSerialization dataWithJSONObject:j options:NSJSONWritingPrettyPrinted error:nil] writeToFile:[self path] atomically:YES];
    }
}

- (BOOL)getCfg:(DSProxyCfg *)out {
    @synchronized (self) {
        if (!self.host.length || self.port <= 0) return NO;
        memset(out, 0, sizeof *out);
        out->type = self.type; out->port = self.port;
        strlcpy(out->host, self.host.UTF8String, sizeof out->host);
        strlcpy(out->user, (self.user ?: @"").UTF8String, sizeof out->user);
        strlcpy(out->pass, (self.pass ?: @"").UTF8String, sizeof out->pass);
        return YES;
    }
}

- (NSString *)summary {
    if (!self.host.length) return @"—";
    return [NSString stringWithFormat:@"%@ %@:%d%@", self.type == DSProxyTypeHTTP ? @"HTTP" : @"SOCKS5", self.host, self.port, self.user.length ? @" 🔐" : @""];
}

- (NSDictionary *)cfDict {
    DSProxyCfg c; if (![self getCfg:&c]) return nil;
    NSString *h = @(c.host); NSNumber *pt = @(c.port);
    if (c.type == DSProxyTypeSOCKS5) {
        NSMutableDictionary *d = [@{ @"SOCKSEnable": @1, @"SOCKSProxy": h, @"SOCKSPort": pt } mutableCopy];
        if (c.user[0]) { d[@"SOCKSUser"] = @(c.user); d[@"SOCKSPassword"] = @(c.pass); }
        return d;
    }
    return @{ @"HTTPEnable": @1, @"HTTPProxy": h, @"HTTPPort": pt, @"HTTPSEnable": @1, @"HTTPSProxy": h, @"HTTPSPort": pt };
}

// يحلّل الرابط ويملأ الحقول فقط (بدون حفظ/تفعيل)
- (BOOL)parseLink:(NSString *)raw error:(NSString **)err {
    #define DSP_ERR(m) do { if (err) *err = (m); return NO; } while (0)
    NSString *l = [raw stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceAndNewlineCharacterSet];
    NSRange nl = [l rangeOfCharacterFromSet:NSCharacterSet.newlineCharacterSet];
    if (nl.location != NSNotFound) l = [l substringToIndex:nl.location];
    if (!l.length) DSP_ERR(@"الرابط فارغ");
    int type = 0, port = 0; NSString *host = nil, *user = nil, *pass = nil;

    if ([l rangeOfString:@"://"].location == NSNotFound) {
        if ([l containsString:@"@"]) return [self parseLink:[@"socks5://" stringByAppendingString:l] error:err];
        NSArray *pp = [l componentsSeparatedByString:@":"];
        if (pp.count == 2) { host = pp[0]; port = [pp[1] intValue]; }
        else if (pp.count == 4) { host = pp[0]; port = [pp[1] intValue]; user = pp[2]; pass = pp[3]; }
        else DSP_ERR(@"صيغة غير مفهومة. أمثلة:\nsocks5://user:pass@host:1080\nhttp://host:8080\nhost:port\nhost:port:user:pass");
        type = DSProxyGuessType(port);
    } else {
        NSURLComponents *uc = [NSURLComponents componentsWithString:l];
        if (!uc || !uc.scheme.length) DSP_ERR(@"الرابط غير صالح (رمّز الرموز الخاصة في اسم المستخدم/كلمة المرور بصيغة %XX)");
        NSString *sch = uc.scheme.lowercaseString, *h = uc.host.lowercaseString;
        BOOL tg = ([sch isEqualToString:@"tg"] && [h isEqualToString:@"socks"]) ||
                  (([sch isEqualToString:@"https"] || [sch isEqualToString:@"http"]) &&
                   ([h isEqualToString:@"t.me"] || [h isEqualToString:@"telegram.me"] || [h isEqualToString:@"telegram.dog"]) &&
                   [uc.path.lowercaseString hasPrefix:@"/socks"]);
        if (tg) {   // رابط بروكسي تيليجرام
            for (NSURLQueryItem *q in uc.queryItems) {
                NSString *k = q.name.lowercaseString;
                if ([k isEqualToString:@"server"]) host = q.value;
                else if ([k isEqualToString:@"port"]) port = [q.value intValue];
                else if ([k isEqualToString:@"user"]) user = q.value;
                else if ([k isEqualToString:@"pass"]) pass = q.value;
            }
            type = DSProxyTypeSOCKS5;
        } else {
            if ([@[@"socks", @"socks5", @"socks5h"] containsObject:sch]) type = DSProxyTypeSOCKS5;
            else if ([@[@"http", @"https"] containsObject:sch]) type = DSProxyTypeHTTP;
            else if ([@[@"socks4", @"socks4a"] containsObject:sch]) DSP_ERR(@"SOCKS4 غير مدعوم. استخدم socks5:// أو http://");
            else if ([@[@"vmess", @"vless", @"trojan", @"ss", @"ssr", @"hysteria", @"hysteria2", @"hy2", @"tuic", @"wireguard"] containsObject:sch])
                DSP_ERR(@"هذا النوع (vmess/vless/trojan/ss...) غير مدعوم لأنه يحتاج نواة Xray/sing-box خارجية. المدعوم: socks5:// و http:// ورابط تيليجرام t.me/socks");
            else DSP_ERR(@"بروتوكول غير معروف. استخدم socks5:// أو http://");
            host = uc.host; port = uc.port.intValue; user = uc.user; pass = uc.password;
            if ([sch isEqualToString:@"socks"] && user.length && !pass.length) {   // socks://base64(user:pass)@host:port
                NSString *dec = DSB64Decode(user);
                NSRange c = [dec rangeOfString:@":"];
                if (dec.length && c.location != NSNotFound) { pass = [dec substringFromIndex:c.location + 1]; user = [dec substringToIndex:c.location]; }
            }
            if (port <= 0) port = (type == DSProxyTypeHTTP) ? 8080 : 1080;
        }
    }
    host = [host stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceAndNewlineCharacterSet];
    if (!host.length) DSP_ERR(@"لم أجد عنوان السيرفر (host) في الرابط");
    if (host.length > 250) DSP_ERR(@"العنوان طويل جداً");
    if (port <= 0 || port > 65535) DSP_ERR(@"المنفذ (port) غير صالح");
    if (user.length > 255 || pass.length > 255) DSP_ERR(@"اسم المستخدم/كلمة المرور أطول من 255");
    @synchronized (self) {
        self.type = type; self.port = port; self.host = host; self.user = user.length ? user : nil; self.pass = pass.length ? pass : nil;
    }
    return YES;
    #undef DSP_ERR
}

- (BOOL)applyLink:(NSString *)raw error:(NSString **)err {
    if (![self parseLink:raw error:err]) return NO;
    self.link = [raw stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceAndNewlineCharacterSet];
    self.enabled = YES; self.lastError = nil;
    [self save];
    return YES;
}
@end

// ---- مصافحة البروكسي (على socket TCP) ----
#define DSP_FAIL(...) do { snprintf(why, wn, __VA_ARGS__); return -1; } while (0)

static void DSPTimeouts(int fd, int sec) {
    struct timeval tv = { sec, 0 };
    setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
    setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof tv);
}
static BOOL DSPSend(int fd, const void *b, size_t n) {
    const uint8_t *p = (const uint8_t *)b;
    while (n) { ssize_t w = send(fd, p, n, 0); if (w < 0) { if (errno == EINTR) continue; return NO; } if (w == 0) return NO; p += w; n -= (size_t)w; }
    return YES;
}
static BOOL DSPRecv(int fd, void *b, size_t n) {
    uint8_t *p = (uint8_t *)b;
    while (n) { ssize_t r = recv(fd, p, n, 0); if (r < 0) { if (errno == EINTR) continue; return NO; } if (r == 0) return NO; p += r; n -= (size_t)r; }
    return YES;
}

static int DSPSocks5(int fd, const DSProxyCfg *c, const struct sockaddr *dst, char *why, size_t wn) {
    BOOL auth = c->user[0] != 0;
    uint8_t hello[4]; size_t hn = 0;
    hello[hn++] = 5; hello[hn++] = auth ? 2 : 1; hello[hn++] = 0; if (auth) hello[hn++] = 2;
    uint8_t rep[2];
    if (!DSPSend(fd, hello, hn) || !DSPRecv(fd, rep, 2)) DSP_FAIL("لا رد من البروكسي. تأكد من النوع (socks5 أم http) والمنفذ");
    if (rep[0] != 5) DSP_FAIL("البروكسي لا يتكلم SOCKS5. جرّب رابط http://");
    if (rep[1] == 0x02) {
        size_t ul = strlen(c->user), pl = strlen(c->pass), n = 0;
        uint8_t buf[520];
        buf[n++] = 1; buf[n++] = (uint8_t)ul; memcpy(buf + n, c->user, ul); n += ul;
        buf[n++] = (uint8_t)pl; memcpy(buf + n, c->pass, pl); n += pl;
        uint8_t ar[2];
        if (!DSPSend(fd, buf, n) || !DSPRecv(fd, ar, 2) || ar[1] != 0) DSP_FAIL("اسم المستخدم أو كلمة المرور مرفوضة");
    } else if (rep[1] != 0) DSP_FAIL("البروكسي يطلب طريقة مصادقة غير مدعومة");

    uint8_t req[24]; size_t n = 0;
    req[n++] = 5; req[n++] = 1; req[n++] = 0;
    if (dst->sa_family == AF_INET) {
        const struct sockaddr_in *a = (const struct sockaddr_in *)dst;
        req[n++] = 1; memcpy(req + n, &a->sin_addr, 4); n += 4; memcpy(req + n, &a->sin_port, 2); n += 2;
    } else {
        const struct sockaddr_in6 *a = (const struct sockaddr_in6 *)dst;
        req[n++] = 4; memcpy(req + n, &a->sin6_addr, 16); n += 16; memcpy(req + n, &a->sin6_port, 2); n += 2;
    }
    uint8_t h[4];
    if (!DSPSend(fd, req, n) || !DSPRecv(fd, h, 4)) DSP_FAIL("انقطع الاتصال أثناء طلب الوجهة");
    if (h[1] != 0) {
        const char *m = "فشل عام";
        switch (h[1]) { case 2: m = "غير مسموح بالوجهة"; break; case 3: m = "الشبكة غير متاحة"; break; case 4: m = "الوجهة غير متاحة"; break;
                        case 5: m = "رفضت الوجهة الاتصال"; break; case 6: m = "انتهت المهلة"; break; case 7: m = "الأمر غير مدعوم"; break; case 8: m = "نوع العنوان غير مدعوم"; break; }
        DSP_FAIL("رفض البروكسي الاتصال بالوجهة: %s", m);
    }
    uint8_t tmp[270]; size_t skip = 0;
    if (h[3] == 1) skip = 6; else if (h[3] == 4) skip = 18;
    else if (h[3] == 3) { uint8_t l; if (!DSPRecv(fd, &l, 1)) DSP_FAIL("رد ناقص من البروكسي"); skip = (size_t)l + 2; }
    else DSP_FAIL("رد غير مفهوم من البروكسي");
    if (skip && !DSPRecv(fd, tmp, skip)) DSP_FAIL("رد ناقص من البروكسي");
    return 0;
}

static int DSPHttp(int fd, const DSProxyCfg *c, const struct sockaddr *dst, char *why, size_t wn) {
    char ip[INET6_ADDRSTRLEN] = {0}, target[96]; int port = 0;
    if (dst->sa_family == AF_INET) {
        const struct sockaddr_in *a = (const struct sockaddr_in *)dst; inet_ntop(AF_INET, &a->sin_addr, ip, sizeof ip); port = ntohs(a->sin_port);
        snprintf(target, sizeof target, "%s:%d", ip, port);
    } else {
        const struct sockaddr_in6 *a = (const struct sockaddr_in6 *)dst; inet_ntop(AF_INET6, &a->sin6_addr, ip, sizeof ip); port = ntohs(a->sin6_port);
        snprintf(target, sizeof target, "[%s]:%d", ip, port);
    }
    NSString *auth = @"";
    if (c->user[0]) {
        NSData *cred = [[NSString stringWithFormat:@"%s:%s", c->user, c->pass] dataUsingEncoding:NSUTF8StringEncoding];
        auth = [NSString stringWithFormat:@"Proxy-Authorization: Basic %@\r\n", [cred base64EncodedStringWithOptions:0]];
    }
    NSData *rq = [[NSString stringWithFormat:@"CONNECT %s HTTP/1.1\r\nHost: %s\r\n%@Proxy-Connection: Keep-Alive\r\n\r\n", target, target, auth] dataUsingEncoding:NSUTF8StringEncoding];
    if (!DSPSend(fd, rq.bytes, rq.length)) DSP_FAIL("تعذّر إرسال الطلب للبروكسي");
    char head[2048]; size_t n = 0;
    while (n < sizeof head - 1) {   // نقرأ بايت بايت حتى لا نبتلع بيانات الاتصال بعد الترويسة
        ssize_t r = recv(fd, head + n, 1, 0);
        if (r < 0 && errno == EINTR) continue;
        if (r <= 0) DSP_FAIL("لا رد من البروكسي. تأكد من النوع (http أم socks5) والمنفذ");
        n++;
        if (n >= 4 && memcmp(head + n - 4, "\r\n\r\n", 4) == 0) break;
    }
    head[n] = 0;
    if (strncmp(head, "HTTP/", 5) != 0) DSP_FAIL("البروكسي لا يتكلم HTTP. جرّب رابط socks5://");
    const char *sp = strchr(head, ' ');
    int code = sp ? atoi(sp + 1) : 0;
    if (code >= 200 && code < 300) return 0;
    if (code == 407) DSP_FAIL("اسم المستخدم أو كلمة المرور مرفوضة (407)");
    DSP_FAIL("رفض البروكسي الطلب (HTTP %d)", code);
}

static BOOL DSProxyResolve(const char *host, int port, int family, struct sockaddr_storage *out, socklen_t *olen) {
    memset(out, 0, sizeof *out);
    struct in_addr a4; struct in6_addr a6;
    BOOL lit4 = inet_pton(AF_INET, host, &a4) == 1, lit6 = !lit4 && inet_pton(AF_INET6, host, &a6) == 1;
    if (lit4 || lit6) {
        if (lit4 && family == AF_INET) {
            struct sockaddr_in *s4 = (struct sockaddr_in *)out; s4->sin_family = AF_INET; s4->sin_len = sizeof *s4; s4->sin_port = htons((uint16_t)port); s4->sin_addr = a4;
            *olen = sizeof *s4; return YES;
        }
        if (lit6 && family == AF_INET6) {
            struct sockaddr_in6 *s6 = (struct sockaddr_in6 *)out; s6->sin6_family = AF_INET6; s6->sin6_len = sizeof *s6; s6->sin6_port = htons((uint16_t)port); s6->sin6_addr = a6;
            *olen = sizeof *s6; return YES;
        }
        return NO;   // عنوان حرفي من عائلة أخرى
    }
    struct addrinfo hints; memset(&hints, 0, sizeof hints);
    hints.ai_family = family; hints.ai_socktype = SOCK_STREAM;
    struct addrinfo *res = NULL; char ps[8]; snprintf(ps, sizeof ps, "%d", port);
    int rc = (orig_getaddrinfo ? orig_getaddrinfo : getaddrinfo)(host, ps, &hints, &res);   // يتجاوز hook حتى لا يتأثر عنوان البروكسي بالقواعد
    BOOL ok = NO;
    if (rc == 0 && res) {
        if (res->ai_addrlen <= sizeof *out) { memcpy(out, res->ai_addr, res->ai_addrlen); *olen = res->ai_addrlen; ok = YES; }
        freeaddrinfo(res);
    }
    return ok;
}

static int (*orig_connect)(int, const struct sockaddr *, socklen_t);

// يتصل بالبروكسي على fd ثم يطلب منه الوجهة dst. 0 = نجاح، -1 = فشل (why)، -2 = لا عنوان بروكسي بنفس عائلة الشبكة
static int DSProxyTunnel(int fd, const DSProxyCfg *c, const struct sockaddr *dst, int timeoutSec, char *why, size_t wn) {
    struct sockaddr_storage px; socklen_t pxl = 0;
    if (!DSProxyResolve(c->host, c->port, dst->sa_family, &px, &pxl)) { snprintf(why, wn, "تعذّر حل عنوان البروكسي"); return -2; }
    int one = 1; setsockopt(fd, SOL_SOCKET, SO_NOSIGPIPE, &one, sizeof one);
    struct timeval oldR = {0, 0}, oldS = {0, 0}; socklen_t tl = sizeof oldR;
    getsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &oldR, &tl); tl = sizeof oldS; getsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &oldS, &tl);
    int fl = fcntl(fd, F_GETFL, 0);
    fcntl(fd, F_SETFL, fl | O_NONBLOCK);
    int rc = (orig_connect ? orig_connect : connect)(fd, (const struct sockaddr *)&px, pxl);
    int cerr = 0;
    if (rc != 0 && errno == EINPROGRESS) {
        struct pollfd pf = { fd, POLLOUT, 0 };
        int pr;
        do { pr = poll(&pf, 1, timeoutSec * 1000); } while (pr < 0 && errno == EINTR);
        if (pr <= 0) { fcntl(fd, F_SETFL, fl); DSP_FAIL("انتهت مهلة الاتصال بالبروكسي"); }
        socklen_t el = sizeof cerr; getsockopt(fd, SOL_SOCKET, SO_ERROR, &cerr, &el);
    } else if (rc != 0) cerr = errno;
    if (cerr) { fcntl(fd, F_SETFL, fl); DSP_FAIL("تعذّر الاتصال بالبروكسي (%s)", strerror(cerr)); }

    fcntl(fd, F_SETFL, fl & ~O_NONBLOCK);
    DSPTimeouts(fd, timeoutSec);
    int r = (c->type == DSProxyTypeHTTP) ? DSPHttp(fd, c, dst, why, wn) : DSPSocks5(fd, c, dst, why, wn);
    setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &oldR, sizeof oldR);
    setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &oldS, sizeof oldS);
    fcntl(fd, F_SETFL, fl);
    return r;
}

// هل نمرّر هذا الاتصال عبر البروكسي؟ (TCP فقط، وجهات عامة فقط)
static BOOL DSProxyShouldTunnel(int fd, const struct sockaddr *sa, socklen_t len) {
    if (!sa) return NO;
    int type = 0; socklen_t tl = sizeof type;
    if (getsockopt(fd, SOL_SOCKET, SO_TYPE, &type, &tl) != 0 || type != SOCK_STREAM) return NO;
    if (sa->sa_family == AF_INET) {
        if (len < sizeof(struct sockaddr_in)) return NO;
        uint32_t v = ntohl(((const struct sockaddr_in *)sa)->sin_addr.s_addr);
        if ((v >> 24) == 0 || (v >> 24) == 127 || (v >> 24) == 10 || (v >> 16) == 0xC0A8 || (v >> 20) == 0xAC1 || (v >> 16) == 0xA9FE || (v >> 24) >= 224) return NO;
        return YES;
    }
    if (sa->sa_family == AF_INET6) {
        if (len < sizeof(struct sockaddr_in6)) return NO;
        const struct in6_addr *a = &((const struct sockaddr_in6 *)sa)->sin6_addr;
        if (IN6_IS_ADDR_LOOPBACK(a) || IN6_IS_ADDR_UNSPECIFIED(a) || IN6_IS_ADDR_LINKLOCAL(a) || IN6_IS_ADDR_MULTICAST(a) ||
            IN6_IS_ADDR_V4MAPPED(a) || (a->s6_addr[0] & 0xFE) == 0xFC) return NO;
        return YES;
    }
    return NO;
}

static int DSProxyConnect(int fd, const struct sockaddr *dst, socklen_t dlen) {
    DSProxyCfg c;
    if (![[DSProxy shared] getCfg:&c]) return orig_connect(fd, dst, dlen);
    char why[160] = {0};
    int rc = DSProxyTunnel(fd, &c, dst, 8, why, sizeof why);
    if (rc == 0) { atomic_fetch_add(&gProxyHits, 1); return 0; }
    if (rc == -2) return orig_connect(fd, dst, dlen);   // البروكسي بلا عنوان بنفس العائلة (IPv4/IPv6): اتصال مباشر
    atomic_fetch_add(&gProxyFails, 1);
    [DSProxy shared].lastError = @(why);
    errno = ECONNREFUSED;
    return -1;
}

// ---- اختبار البروكسي: يفتح نفقاً إلى 1.1.1.1:80 ويقرأ IP الخروج ----
static void DSProxyTest(void (^done)(NSString *report, BOOL ok)) {
    dispatch_async(dispatch_get_global_queue(QOS_CLASS_USER_INITIATED, 0), ^{
        __block NSString *report = nil; __block BOOL ok = NO;
        DSProxyCfg c;
        if (![[DSProxy shared] getCfg:&c]) { report = @"لا يوجد بروكسي محفوظ"; }
        else {
            int fd = socket(AF_INET, SOCK_STREAM, 0);
            struct sockaddr_in dst; memset(&dst, 0, sizeof dst);
            dst.sin_family = AF_INET; dst.sin_len = sizeof dst; dst.sin_port = htons(80); inet_pton(AF_INET, "1.1.1.1", &dst.sin_addr);
            char why[160] = {0};
            struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
            int rc = fd >= 0 ? DSProxyTunnel(fd, &c, (struct sockaddr *)&dst, 8, why, sizeof why) : -1;
            clock_gettime(CLOCK_MONOTONIC, &t1);
            int ms = (int)((t1.tv_sec - t0.tv_sec) * 1000 + (t1.tv_nsec - t0.tv_nsec) / 1000000);
            if (fd < 0) { report = @"تعذّر إنشاء socket"; }
            else if (rc != 0) { report = [NSString stringWithFormat:@"%@\n\n%@", [[DSProxy shared] summary], @(why[0] ? why : "فشل غير معروف")]; }
            else {
                ok = YES;
                NSString *exitInfo = @"(لم أستطع قراءة IP الخروج)";
                DSPTimeouts(fd, 8);
                const char *rq = "GET /cdn-cgi/trace HTTP/1.1\r\nHost: 1.1.1.1\r\nUser-Agent: curl/8\r\nConnection: close\r\n\r\n";
                if (DSPSend(fd, rq, strlen(rq))) {
                    char buf[4096]; size_t n = 0;
                    while (n < sizeof buf - 1) { ssize_t r = recv(fd, buf + n, sizeof buf - 1 - n, 0); if (r <= 0) break; n += (size_t)r; }
                    buf[n] = 0;
                    NSString *body = [NSString stringWithUTF8String:buf] ?: @"";
                    NSString *ip = nil, *loc = nil;
                    for (NSString *ln in [body componentsSeparatedByString:@"\n"]) {
                        NSString *t = [ln stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceAndNewlineCharacterSet];
                        if ([t hasPrefix:@"ip="]) ip = [t substringFromIndex:3];
                        else if ([t hasPrefix:@"loc="]) loc = [t substringFromIndex:4];
                    }
                    if (ip.length) exitInfo = [NSString stringWithFormat:@"IP الخروج: %@%@", ip, loc.length ? [NSString stringWithFormat:@"  (%@)", loc] : @""];
                }
                report = [NSString stringWithFormat:@"%@\nزمن الاتصال: %d ms\n%@", [[DSProxy shared] summary], ms, exitInfo];
            }
            if (fd >= 0) close(fd);
        }
        dispatch_async(dispatch_get_main_queue(), ^{ done(report, ok); });
    });
}

// ---- NSURLSession: حقن البروكسي في الإعدادات عند إنشائها ----
typedef void *(*DSNWMakeEp)(const char *, const char *);
typedef void *(*DSNWMakeProxy1)(void *);
typedef void *(*DSNWMakeProxy2)(void *, void *);
typedef void (*DSNWSetCred)(void *, const char *, const char *);

static void DSProxyApplyModern(NSURLSessionConfiguration *cfg, const DSProxyCfg *c) {   // iOS 17+: يدعم المصادقة بشكل أصلي
    if (![cfg respondsToSelector:NSSelectorFromString(@"setProxyConfigurations:")]) return;
    DSNWMakeEp mkEp = (DSNWMakeEp)dlsym(RTLD_DEFAULT, "nw_endpoint_create_host");
    DSNWMakeProxy1 mkSocks = (DSNWMakeProxy1)dlsym(RTLD_DEFAULT, "nw_proxy_config_create_socksv5");
    DSNWMakeProxy2 mkHttp = (DSNWMakeProxy2)dlsym(RTLD_DEFAULT, "nw_proxy_config_create_http_connect");
    DSNWSetCred setCred = (DSNWSetCred)dlsym(RTLD_DEFAULT, "nw_proxy_config_set_username_and_password");
    if (!mkEp || (c->type == DSProxyTypeSOCKS5 ? !mkSocks : !mkHttp)) return;
    char ps[8]; snprintf(ps, sizeof ps, "%d", c->port);
    void *ep = mkEp(c->host, ps); if (!ep) return;
    id epObj = (__bridge_transfer id)ep;
    void *pc = (c->type == DSProxyTypeSOCKS5) ? mkSocks(ep) : mkHttp(ep, NULL);
    if (!pc) return;
    id pcObj = (__bridge_transfer id)pc;
    if (c->user[0] && setCred) setCred(pc, c->user, c->pass);
    (void)epObj;
    @try { [cfg setValue:@[pcObj] forKey:@"proxyConfigurations"]; } @catch (__unused id e) {}
}

static NSURLSessionConfiguration *DSProxyApply(id cfgObj) {
    if (gQoSMode >= 2 && [cfgObj isKindOfClass:NSURLSessionConfiguration.class])   // QoS «كل اللعبة»: طلبات HTTP/WebSocket تفاعلية
        ((NSURLSessionConfiguration *)cfgObj).networkServiceType = NSURLNetworkServiceTypeResponsiveData;
    if (!gProxyOn || ![cfgObj isKindOfClass:NSURLSessionConfiguration.class]) return cfgObj;
    NSURLSessionConfiguration *cfg = (NSURLSessionConfiguration *)cfgObj;
    DSProxyCfg c; if (![[DSProxy shared] getCfg:&c]) return cfg;
    cfg.connectionProxyDictionary = [[DSProxy shared] cfDict];
    DSProxyApplyModern(cfg, &c);
    return cfg;
}

static void DSInstallProxySessionHooks(void) {
    Class cfgCls = NSURLSessionConfiguration.class;
    for (NSString *n in @[@"defaultSessionConfiguration", @"ephemeralSessionConfiguration"]) {
        SEL sel = NSSelectorFromString(n);
        Method m = class_getClassMethod(cfgCls, sel);
        if (!m) continue;
        IMP orig = method_getImplementation(m);
        id blk = ^id(__unsafe_unretained id self_) {
            id c = ((id (*)(id, SEL))orig)(self_, sel);
            DSProxyApply(c);
            return c;
        };
        method_setImplementation(m, imp_implementationWithBlock(blk));
    }
    Class sess = NSURLSession.class;
    SEL s1 = @selector(sessionWithConfiguration:), s2 = @selector(sessionWithConfiguration:delegate:delegateQueue:);
    Method m1 = class_getClassMethod(sess, s1);
    if (m1) {
        IMP o1 = method_getImplementation(m1);
        id b1 = ^id(__unsafe_unretained id self_, __unsafe_unretained id cfg) { DSProxyApply(cfg); return ((id (*)(id, SEL, id))o1)(self_, s1, cfg); };
        method_setImplementation(m1, imp_implementationWithBlock(b1));
    }
    Method m2 = class_getClassMethod(sess, s2);
    if (m2) {
        IMP o2 = method_getImplementation(m2);
        id b2 = ^id(__unsafe_unretained id self_, __unsafe_unretained id cfg, __unsafe_unretained id del, __unsafe_unretained id q) {
            DSProxyApply(cfg); return ((id (*)(id, SEL, id, id, id))o2)(self_, s2, cfg, del, q);
        };
        method_setImplementation(m2, imp_implementationWithBlock(b2));
    }
}

// يحفظ آخر سيرفر TCP عام (IPv4) اتصلت به اللعبة، ليقيس PING نحوه. الفحوص رخيصة وتعمل فقط وPING مفعّل.
static void DSPingNoteConnect(int fd, const struct sockaddr *sa, socklen_t len) {
    if (!gPingOn || !sa || sa->sa_family != AF_INET || len < sizeof(struct sockaddr_in)) return;
    int ty = 0; socklen_t tl = sizeof ty;
    if (getsockopt(fd, SOL_SOCKET, SO_TYPE, &ty, &tl) != 0 || ty != SOCK_STREAM) return;
    const struct sockaddr_in *in = (const struct sockaddr_in *)sa;
    uint32_t ip = ntohl(in->sin_addr.s_addr); uint16_t port = ntohs(in->sin_port);
    if (!port) return;
    uint8_t a = (uint8_t)(ip >> 24), b = (uint8_t)((ip >> 16) & 255);
    if (a == 0 || a == 10 || a == 127 || a >= 224 || (a == 172 && b >= 16 && b <= 31) || (a == 192 && b == 168) || (a == 169 && b == 254)) return;
    if (ip == 0x08080808 || ip == 0x01010101) return;   // أهداف DNS/القياس نفسها لا تهمنا
    gPingGameIP = in->sin_addr.s_addr; gPingGamePort = in->sin_port;
}

#pragma mark - أولوية QoS داخل اللعبة: شبكة (UDP/TCP) + خيوط الصوت والاتصال
// الأوضاع: 0 = OFF · 1 = الصوت (UDP بفئة «صوت» + رفع خيوط Agora/Zego/NTgCalls)
//          2 = كل اللعبة (+ TCP تفاعلي + إعدادات NSURLSession + بقية خيوط اللعبة بمستوى أقل من الصوت)
// الشبكة: الأولوية تتحدد عند إنشاء السوكت (hook على socket) فتشمل كل مكتبات اللعبة مهما كانت دالة الإرسال (send/sendto/write).
// ملاحظة: أثرها يظهر لما الجهاز أو الواي فاي مشغول؛ لا تقلل بعد السيرفر ولا تسرّع الإنترنت نفسه.
#ifndef SO_TRAFFIC_CLASS
#define SO_TRAFFIC_CLASS 0x1086
#endif
#ifndef SO_TC_VI
#define SO_TC_VI 700
#endif
#ifndef SO_TC_VO
#define SO_TC_VO 800
#endif
static uint8_t gQoSSeen[512];   // خريطة بتات: fd < 4096 وُسم مسبقاً (لو أُعيد استخدام الرقم نخسر التحسين فقط، لا يتعطل شي)

static void DSQoSTagFd(int fd, int type) {   // type: SOCK_DGRAM أو SOCK_STREAM
    int tc, tos;
    if (type == SOCK_DGRAM && gQoSMode >= 1) { tc = SO_TC_VO; tos = 0xB8; }          // صوت: DSCP 46 (EF)
    else if (type == SOCK_STREAM && gQoSMode >= 2) { tc = SO_TC_VI; tos = 0x88; }    // تفاعلي: DSCP 34 (AF41)
    else return;
    setsockopt(fd, SOL_SOCKET, SO_TRAFFIC_CLASS, &tc, sizeof tc);
    setsockopt(fd, IPPROTO_IP, IP_TOS, &tos, sizeof tos);            // IPv4 (يفشل بصمت على سوكت IPv6)
#ifdef IPV6_TCLASS
    setsockopt(fd, IPPROTO_IPV6, IPV6_TCLASS, &tos, sizeof tos);     // IPv6 (يفشل بصمت على سوكت IPv4)
#endif
}

// وسم متأخر للسوكتات التي أُنشئت قبل تفعيل الخيار (يُستدعى من connect/sendto)
static void DSQoSApply(int fd) {
    if (gQoSMode < 1 || fd < 0 || fd >= 4096) return;
    uint8_t bit = (uint8_t)(1u << (fd & 7));
    if (gQoSSeen[fd >> 3] & bit) return;
    int ty = 0; socklen_t tl = sizeof ty;
    if (getsockopt(fd, SOL_SOCKET, SO_TYPE, &ty, &tl) != 0 || (ty != SOCK_DGRAM && ty != SOCK_STREAM)) return;
    struct sockaddr_storage ss; socklen_t sl = sizeof ss;
    if (getsockname(fd, (struct sockaddr *)&ss, &sl) != 0 || (ss.ss_family != AF_INET && ss.ss_family != AF_INET6)) return;   // شبكة فقط (لا unix)
    gQoSSeen[fd >> 3] |= bit;
    DSQoSTagFd(fd, ty);
}
static void DSQoSForget(int fd) { if (fd >= 0 && fd < 4096) gQoSSeen[fd >> 3] &= (uint8_t)~(1u << (fd & 7)); }

static int (*orig_socket)(int, int, int);
static int hook_socket(int domain, int type, int proto) {
    int fd = orig_socket(domain, type, proto);
    if (fd >= 0 && gQoSMode >= 1 && (domain == AF_INET || domain == AF_INET6)) {
        DSQoSTagFd(fd, type);
        if (fd < 4096) gQoSSeen[fd >> 3] |= (uint8_t)(1u << (fd & 7));
    }
    return fd;
}

// ---- أولوية الخيوط: خيوط محركات الصوت/الاتصال (Agora / Zego / NTgCalls) = USER_INTERACTIVE ----
// وبالوضع 2: بقية خيوط اللعبة (pthread_create من الملف التنفيذي ومكتباته غير النظام) = USER_INITIATED (أقل من خيط الواجهة حتى ما نخنقه).
// تُطبَّق على الخيوط التي تُنشأ بعد التفعيل؛ الخيوط التي اشتغلت قبل ذلك تحتاج إعادة فتح اللعبة.
static int (*orig_pthread_create)(pthread_t *, const pthread_attr_t *, void *(*)(void *), void *);
typedef struct { void *(*fn)(void *); void *arg; int cls; } DSThrBoot;

static void *DSThrTramp(void *p) {
    DSThrBoot b = *(DSThrBoot *)p; free(p);
    pthread_set_qos_class_self_np(b.cls == 2 ? QOS_CLASS_USER_INTERACTIVE : QOS_CLASS_USER_INITIATED, 0);
    return b.fn(b.arg);
}

static int DSThrClass(void *fn) {   // 2 = خيط وسائط/اتصال · 1 = خيط لعبة عادي (وضع 2 فقط) · 0 = لا يُمس
    Dl_info di;
    if (!dladdr(fn, &di) || !di.dli_fname) return 0;
    const char *path = di.dli_fname;
    if (strcasestr(path, "agora") || strcasestr(path, "zego") || strcasestr(path, "ntgcalls")) return 2;
    if (gQoSMode < 2) return 0;
    if (!strncmp(path, "/System/", 8) || !strncmp(path, "/usr/", 5) || !strncmp(path, "/Developer/", 11)) return 0;
    static const void *own;
    if (!own) { Dl_info o; if (dladdr((const void *)&DSThrClass, &o)) own = o.dli_fbase; }
    if (own && di.dli_fbase == own) return 0;   // خيوط الأداة نفسها لا تُمس
    return 1;
}

static int hook_pthread_create(pthread_t *t, const pthread_attr_t *a, void *(*fn)(void *), void *arg) {
    int cls = (gQoSMode >= 1 && fn) ? DSThrClass((void *)fn) : 0;
    if (cls) {
        DSThrBoot *b = (DSThrBoot *)malloc(sizeof *b);
        if (b) {
            b->fn = fn; b->arg = arg; b->cls = cls;
            int r = orig_pthread_create(t, a, DSThrTramp, b);
            if (r != 0) free(b);
            return r;
        }
    }
    return orig_pthread_create(t, a, fn, arg);
}

static int hook_connect(int fd, const struct sockaddr *sa, socklen_t len) {
    DSQoSForget(fd); DSQoSApply(fd);
    DSPingNoteConnect(fd, sa, len);
    DSNoteSockaddr(sa, len, "connect");
    struct sockaddr_storage ss;
    if (DSRewriteSockaddr(sa, len, &ss)) sa = (const struct sockaddr *)&ss;
    if (gProxyOn && DSProxyShouldTunnel(fd, sa, len)) return DSProxyConnect(fd, sa, len);   // عبر البروكسي (SOCKS5 / HTTP CONNECT)
    return orig_connect(fd, sa, len);
}

static ssize_t hook_sendto(int fd, const void *buf, size_t n, int flags, const struct sockaddr *dst, socklen_t dlen) {
    DSQoSApply(fd);
    if (dst) DSNoteSockaddr(dst, dlen, "udp");
    struct sockaddr_storage ss;
    if (dst && DSRewriteSockaddr(dst, dlen, &ss)) return orig_sendto(fd, buf, n, flags, (const struct sockaddr *)&ss, dlen);
    return orig_sendto(fd, buf, n, flags, dst, dlen);
}

static void DSURL(NSURL *u, NSString *src) {
    NSString *h = u.host;
    if ([h.lowercaseString hasSuffix:@"nextdns.io"]) return;  // لا تسجّل طلبات الأداة نفسها
    if (h.length) [[DSStore shared] recordHost:h ips:nil source:src failed:NO];
}

#pragma mark - Built-in hook engine (no Substrate / ElleKit needed)

// 1) دوال C (getaddrinfo, connect, ...) عبر إعادة ربط مؤشرات الرموز في كل صور Mach-O المحمّلة
typedef struct { const char *name; void *replacement; BOOL appOnly; } DSRebind;   // appOnly: لا يُطبَّق على مكتبات النظام ولا على الأداة نفسها ولا على محركات الصوت
static DSRebind gRebinds[16];
static BOOL gRebindSkipAppOnly = NO;      // تُضبط لكل صورة قبل المرور على أقسامها
static const void *gGSOwnBase = NULL;     // عنوان صورة الأداة نفسها

// صور لا نريد تسريع ساعتها: النظام، الأداة نفسها، ومحركات الصوت/المكالمات (حتى لا ينقطع الصوت أو الاتصال)
static BOOL DSGSImageExcluded(const char *path, const void *base) {
    if (!gGSOwnBase) { Dl_info o; if (dladdr((const void *)&DSGSImageExcluded, &o)) gGSOwnBase = o.dli_fbase; }
    if (base && base == gGSOwnBase) return YES;
    if (!path) return NO;
    if (!strncmp(path, "/System/", 8) || !strncmp(path, "/usr/lib/", 9) || !strncmp(path, "/usr/libexec/", 13) || !strncmp(path, "/Developer/", 11)) return YES;
    if (strcasestr(path, "agora") || strcasestr(path, "zego") || strcasestr(path, "ntgcalls")) return YES;
    return NO;
}
static int gRebindCount = 0;

static BOOL DSSetProt(void *addr, size_t size, vm_prot_t prot, BOOL copy) {
    uintptr_t pg = (uintptr_t)vm_page_size;
    uintptr_t start = (uintptr_t)addr & ~(pg - 1);
    uintptr_t end = ((uintptr_t)addr + size + pg - 1) & ~(pg - 1);
    return vm_protect(mach_task_self(), (vm_address_t)start, (vm_size_t)(end - start), 0,
                      copy ? (prot | VM_PROT_COPY) : prot) == KERN_SUCCESS;
}

static void DSRebindSection(const struct section_64 *sect, intptr_t slide, const struct nlist_64 *symtab,
                            const char *strtab, const uint32_t *indirect) {
    const uint32_t *idx = indirect + sect->reserved1;
    void **slots = (void **)((uintptr_t)slide + (uintptr_t)sect->addr);
    size_t count = (size_t)(sect->size / sizeof(void *));
    BOOL isConst = strncmp(sect->segname, "__DATA_CONST", 16) == 0;
    BOOL unlocked = NO;
    for (size_t i = 0; i < count; i++) {
        uint32_t si = idx[i];
        if (si == INDIRECT_SYMBOL_ABS || si == INDIRECT_SYMBOL_LOCAL || si == (INDIRECT_SYMBOL_LOCAL | INDIRECT_SYMBOL_ABS)) continue;
        const char *name = strtab + symtab[si].n_un.n_strx;
        if (!name[0] || !name[1]) continue;
        for (int k = 0; k < gRebindCount; k++) {
            if (strcmp(name + 1, gRebinds[k].name) != 0) continue;
            if (gRebinds[k].appOnly && gRebindSkipAppOnly) break;
            if (slots[i] == gRebinds[k].replacement) break;
            if (isConst && !unlocked) {
                if (!DSSetProt(slots, (size_t)sect->size, VM_PROT_READ | VM_PROT_WRITE, YES)) return;
                unlocked = YES;
            }
            slots[i] = gRebinds[k].replacement;
            break;
        }
    }
    if (isConst && unlocked) DSSetProt(slots, (size_t)sect->size, VM_PROT_READ, NO);
}

static void DSRebindImage(const struct mach_header *mh, intptr_t slide) {
    if (!mh || mh->magic != MH_MAGIC_64) return;
    { Dl_info di; memset(&di, 0, sizeof di); dladdr(mh, &di); gRebindSkipAppOnly = DSGSImageExcluded(di.dli_fname, (const void *)mh); }
    const struct mach_header_64 *h = (const struct mach_header_64 *)mh;
    const struct segment_command_64 *linkedit = NULL;
    const struct symtab_command *stc = NULL;
    const struct dysymtab_command *dsc = NULL;
    uintptr_t cur = (uintptr_t)h + sizeof(struct mach_header_64);
    for (uint32_t i = 0; i < h->ncmds; i++) {
        const struct load_command *lc = (const struct load_command *)cur;
        if (lc->cmd == LC_SEGMENT_64) {
            const struct segment_command_64 *seg = (const struct segment_command_64 *)cur;
            if (strcmp(seg->segname, SEG_LINKEDIT) == 0) linkedit = seg;
        } else if (lc->cmd == LC_SYMTAB) stc = (const struct symtab_command *)cur;
        else if (lc->cmd == LC_DYSYMTAB) dsc = (const struct dysymtab_command *)cur;
        cur += lc->cmdsize;
    }
    if (!linkedit || !stc || !dsc || dsc->nindirectsyms == 0) return;
    uintptr_t base = (uintptr_t)slide + (uintptr_t)linkedit->vmaddr - (uintptr_t)linkedit->fileoff;
    const struct nlist_64 *symtab = (const struct nlist_64 *)(base + stc->symoff);
    const char *strtab = (const char *)(base + stc->stroff);
    const uint32_t *indirect = (const uint32_t *)(base + dsc->indirectsymoff);
    cur = (uintptr_t)h + sizeof(struct mach_header_64);
    for (uint32_t i = 0; i < h->ncmds; i++) {
        const struct load_command *lc = (const struct load_command *)cur;
        if (lc->cmd == LC_SEGMENT_64) {
            const struct segment_command_64 *seg = (const struct segment_command_64 *)cur;
            if (strcmp(seg->segname, "__DATA") == 0 || strncmp(seg->segname, "__DATA_CONST", 16) == 0) {
                const struct section_64 *secs = (const struct section_64 *)(cur + sizeof(struct segment_command_64));
                for (uint32_t j = 0; j < seg->nsects; j++) {
                    uint32_t type = secs[j].flags & SECTION_TYPE;
                    if (type == S_LAZY_SYMBOL_POINTERS || type == S_NON_LAZY_SYMBOL_POINTERS)
                        DSRebindSection(&secs[j], slide, symtab, strtab, indirect);
                }
            }
        }
        cur += lc->cmdsize;
    }
}

#define DS_ADD_REBIND(sym, origvar, hookfn) do { \
    void *p_ = dlsym(RTLD_DEFAULT, sym); \
    if (p_) { origvar = (__typeof__(origvar))p_; \
              gRebinds[gRebindCount].name = sym; gRebinds[gRebindCount].replacement = (void *)hookfn; gRebindCount++; } \
} while (0)

static OSStatus (*orig_AudioUnitSetProperty)(AudioUnit, AudioUnitPropertyID, AudioUnitScope, AudioUnitElement, const void *, UInt32);
static OSStatus hook_AudioUnitSetProperty(AudioUnit, AudioUnitPropertyID, AudioUnitScope, AudioUnitElement, const void *, UInt32);

#pragma mark - تسريع اللعبة (Game Speed) — تسريع/إبطاء ساعة التطبيق المضيف

// فكرة العمل (مثل مسرّعات الألعاب): نلتفّ على دوال الوقت التي تقرأها اللعبة فقط، فتظن أن الوقت يمرّ بمعامل s.
//   الوقت الافتراضي = الوقت الحقيقي + extra ، حيث extra يتراكم بمعدل (s-1) كل ثانية حقيقية.
// عند تغيير المعامل نثبّت extra الحالي أولاً فيبقى الوقت متصلاً (لا قفزات ولا رجوع للخلف).
// ملاحظة: بعد التسريع يبقى extra كما هو عند الرجوع إلى x1 (الوقت لا يرجع للخلف) — إعادة فتح التطبيق تصفّره.
static os_unfair_lock gGSLock = OS_UNFAIR_LOCK_INIT;
static double gGSScale = 1.0;
static double gGSExtraNs = 0.0;
static uint64_t gGSAnchor = 0;
static mach_timebase_info_data_t gGSTb;
static BOOL gGSReady = NO;

static uint64_t (*orig_mach_absolute_time)(void);
static int (*orig_clock_gettime)(clockid_t, struct timespec *);
static uint64_t (*orig_clock_gettime_nsec_np)(clockid_t);
static int (*orig_gettimeofday)(struct timeval *, void *);
static CFTimeInterval (*orig_CACurrentMediaTime)(void);

static double DSGSExtraNs(void) {
    if (!gGSReady) return 0.0;
    os_unfair_lock_lock(&gGSLock);
    double extra = gGSExtraNs;
    if (gGSScale != 1.0) {
        uint64_t now = orig_mach_absolute_time();
        extra += (double)(now - gGSAnchor) * gGSTb.numer / gGSTb.denom * (gGSScale - 1.0);
    }
    os_unfair_lock_unlock(&gGSLock);
    return extra;
}

static void DSGSSetScale(double s) {
    if (!gGSReady) return;
    if (s < 0.1) s = 0.1;
    if (s > 600.0) s = 600.0;
    os_unfair_lock_lock(&gGSLock);
    uint64_t now = orig_mach_absolute_time();
    if (gGSScale != 1.0) gGSExtraNs += (double)(now - gGSAnchor) * gGSTb.numer / gGSTb.denom * (gGSScale - 1.0);
    gGSAnchor = now;
    gGSScale = s;
    os_unfair_lock_unlock(&gGSLock);
}

static double DSGSGetScale(void) { return gGSScale; }

static BOOL DSGSClockAffected(clockid_t c) {
    return c == CLOCK_REALTIME || c == CLOCK_MONOTONIC || c == CLOCK_MONOTONIC_RAW || c == CLOCK_UPTIME_RAW;
}

static uint64_t hook_mach_absolute_time(void) {
    uint64_t t = orig_mach_absolute_time();
    double ex = DSGSExtraNs();
    if (ex == 0.0) return t;
    return t + (uint64_t)(int64_t)(ex * gGSTb.denom / gGSTb.numer);
}

static int hook_clock_gettime(clockid_t c, struct timespec *ts) {
    int r = orig_clock_gettime(c, ts);
    if (r == 0 && ts && DSGSClockAffected(c)) {
        double ex = DSGSExtraNs();
        if (ex != 0.0) {
            int64_t ns = (int64_t)ts->tv_sec * 1000000000LL + (int64_t)ts->tv_nsec + (int64_t)ex;
            ts->tv_sec = (time_t)(ns / 1000000000LL);
            ts->tv_nsec = (long)(ns % 1000000000LL);
            if (ts->tv_nsec < 0) { ts->tv_nsec += 1000000000L; ts->tv_sec -= 1; }
        }
    }
    return r;
}

static uint64_t hook_clock_gettime_nsec_np(clockid_t c) {
    uint64_t r = orig_clock_gettime_nsec_np(c);
    if (r && DSGSClockAffected(c)) {
        double ex = DSGSExtraNs();
        if (ex != 0.0) r += (uint64_t)(int64_t)ex;
    }
    return r;
}

static int hook_gettimeofday(struct timeval *tv, void *tz) {
    int r = orig_gettimeofday(tv, tz);
    if (r == 0 && tv) {
        double ex = DSGSExtraNs();
        if (ex != 0.0) {
            int64_t us = (int64_t)tv->tv_sec * 1000000LL + (int64_t)tv->tv_usec + (int64_t)(ex / 1000.0);
            tv->tv_sec = (time_t)(us / 1000000LL);
            tv->tv_usec = (suseconds_t)(us % 1000000LL);
            if (tv->tv_usec < 0) { tv->tv_usec += 1000000; tv->tv_sec -= 1; }
        }
    }
    return r;
}

static CFTimeInterval hook_CACurrentMediaTime(void) {
    return orig_CACurrentMediaTime() + DSGSExtraNs() / 1e9;
}

#define DS_ADD_REBIND_APP(sym, origvar, hookfn) do { \
    int c_ = gRebindCount; \
    DS_ADD_REBIND(sym, origvar, hookfn); \
    if (gRebindCount > c_) gRebinds[c_].appOnly = YES; \
} while (0)

static void DSGSInstall(void) {
    mach_timebase_info(&gGSTb);
    if (gGSTb.denom == 0) return;
    DS_ADD_REBIND_APP("mach_absolute_time", orig_mach_absolute_time, hook_mach_absolute_time);
    if (!orig_mach_absolute_time) return;                    // بدون الساعة الأصلية لا نفعّل شيئاً
    DS_ADD_REBIND_APP("clock_gettime", orig_clock_gettime, hook_clock_gettime);
    DS_ADD_REBIND_APP("clock_gettime_nsec_np", orig_clock_gettime_nsec_np, hook_clock_gettime_nsec_np);
    DS_ADD_REBIND_APP("gettimeofday", orig_gettimeofday, hook_gettimeofday);
    DS_ADD_REBIND_APP("CACurrentMediaTime", orig_CACurrentMediaTime, hook_CACurrentMediaTime);
    gGSReady = YES;
}

// الحركات الأصلية (CoreAnimation) تتبع ساعة خادم الرسم لا ساعة التطبيق، فنسرّعها عبر layer.speed لنوافذ التطبيق فقط
static void DSGSApplyLayerSpeed(void) {
    float s = (float)gGSScale;
    for (UIScene *sc in UIApplication.sharedApplication.connectedScenes) {
        if (![sc isKindOfClass:UIWindowScene.class]) continue;
        for (UIWindow *w in ((UIWindowScene *)sc).windows) {
            if (w.windowLevel >= UIWindowLevelAlert) continue;   // نوافذ الأداة وتنبيهات النظام لا تُمسّ
            if (fabsf(w.layer.speed - s) > 0.001f) w.layer.speed = s;
        }
    }
}

static void DSInstallCHooks(void) {
    DS_ADD_REBIND("getaddrinfo", orig_getaddrinfo, hook_getaddrinfo);
    DS_ADD_REBIND("gethostbyname", orig_gethostbyname, hook_gethostbyname);
    DS_ADD_REBIND("connect", orig_connect, hook_connect);
    DS_ADD_REBIND("sendto", orig_sendto, hook_sendto);
    DS_ADD_REBIND("socket", orig_socket, hook_socket);                    // QoS: وسم كل سوكت عند إنشائه
    DS_ADD_REBIND("pthread_create", orig_pthread_create, hook_pthread_create);   // QoS: أولوية خيوط الصوت/اللعبة
    DS_ADD_REBIND("AudioUnitSetProperty", orig_AudioUnitSetProperty, hook_AudioUnitSetProperty);   // السرعة الحية لكل الصوت
    DSGSInstall();   // تسريع اللعبة: دوال الوقت (appOnly)
    _dyld_register_func_for_add_image(DSRebindImage);  // يمرّ على الصور الحالية ثم أي صورة جديدة
}

// 2) NSURLSession عبر ObjC runtime
static BOOL DSClassOwns(Class c, SEL s) {
    unsigned n = 0; BOOL found = NO;
    Method *list = class_copyMethodList(c, &n);
    for (unsigned i = 0; i < n; i++) if (method_getName(list[i]) == s) { found = YES; break; }
    free(list);
    return found;
}

static void DSHookURLMethod(Class base, Class concrete, const char *selName, NSString *src) {
    SEL sel = sel_registerName(selName);
    Class target = (concrete && concrete != base && DSClassOwns(concrete, sel)) ? concrete : base;
    Method m = class_getInstanceMethod(target, sel);
    if (!m) return;
    IMP orig = method_getImplementation(m);
    id (^blk)(__unsafe_unretained id, __unsafe_unretained id, __unsafe_unretained id, __unsafe_unretained id) =
        ^id(__unsafe_unretained id obj, __unsafe_unretained id a, __unsafe_unretained id b, __unsafe_unretained id c) {
            NSURL *u = nil;
            if ([a isKindOfClass:NSURLRequest.class]) u = ((NSURLRequest *)a).URL;
            else if ([a isKindOfClass:NSURL.class]) u = (NSURL *)a;
            DSURL(u, src);
            return ((id (*)(id, SEL, id, id, id))orig)(obj, sel, a, b, c);
        };
    method_setImplementation(m, imp_implementationWithBlock(blk));
}

static void DSInstallURLSessionHooks(void) {
    Class base = NSURLSession.class;
    Class concrete = [NSURLSession sharedSession].class;
    DSHookURLMethod(base, concrete, "dataTaskWithRequest:", @"http");
    DSHookURLMethod(base, concrete, "dataTaskWithRequest:completionHandler:", @"http");
    DSHookURLMethod(base, concrete, "dataTaskWithURL:", @"http");
    DSHookURLMethod(base, concrete, "dataTaskWithURL:completionHandler:", @"http");
    DSHookURLMethod(base, concrete, "uploadTaskWithRequest:fromData:", @"upload");
    DSHookURLMethod(base, concrete, "uploadTaskWithRequest:fromData:completionHandler:", @"upload");
    DSHookURLMethod(base, concrete, "uploadTaskWithRequest:fromFile:", @"upload");
    DSHookURLMethod(base, concrete, "downloadTaskWithRequest:", @"download");
    DSHookURLMethod(base, concrete, "downloadTaskWithURL:", @"download");
    DSHookURLMethod(base, concrete, "webSocketTaskWithURL:", @"ws");
    DSHookURLMethod(base, concrete, "webSocketTaskWithRequest:", @"ws");
    DSInstallProxySessionHooks();
}

#pragma mark - AUTO TEST engine (ALL / CHAT)

static NSString *const ASTestDidUpdateNotification = @"ASTestDidUpdateNotification";
static NSString *const ASTestLogNotification = @"ASTestLogNotification";

typedef NS_ENUM(NSInteger, ASTestMode) {
    ASTestModeOff = 0,
    ASTestModeAll = 1,    // الخيار الأول: كل النطاقات وIP/DNS
    ASTestModeChat = 2    // الخيار الثاني: IP/DNS الدردشة والكتابة أونلاين
};

static double ASNow(void) {
    struct timespec ts; clock_gettime(CLOCK_REALTIME, &ts);
    return (double)ts.tv_sec + ts.tv_nsec / 1e9;
}

static BOOL ASIsPublicIP(NSString *ip) {
    if (ip.length == 0) return NO;
    struct in_addr a4; struct in6_addr a6;
    if (inet_pton(AF_INET, ip.UTF8String, &a4) == 1) {
        uint32_t v = ntohl(a4.s_addr);
        if ((v >> 24) == 0 || (v >> 24) == 127 || (v >> 24) == 10 ||
            (v >> 16) == 0xC0A8 || (v >> 20) == 0xAC1 || (v >> 16) == 0xA9FE) return NO;
        return YES;
    }
    if (inet_pton(AF_INET6, ip.UTF8String, &a6) == 1) {
        if (IN6_IS_ADDR_LOOPBACK(&a6) || IN6_IS_ADDR_UNSPECIFIED(&a6) ||
            IN6_IS_ADDR_LINKLOCAL(&a6) || (a6.s6_addr[0] & 0xFE) == 0xFC) return NO;
        return YES;
    }
    return NO;
}

// يحل النطاق عبر DNS النظام أولاً، ثم 8.8.8.8 كاحتياطي. يتجاوز hook إعادة التوجيه
// حتى لا نختبر 8.8.8.8 بدل السيرفر الحقيقي.
static NSArray<NSString *> *ASResolveHost(NSString *host, double *msOut) {
    NSMutableArray *out = [NSMutableArray array];
    if (!host.length) { if (msOut) *msOut = 0; return out; }
    double t0 = ASNow();
    struct addrinfo hints; memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_UNSPEC; hints.ai_socktype = SOCK_STREAM;
    struct addrinfo *res = NULL;
    int r = orig_getaddrinfo ? orig_getaddrinfo(host.UTF8String, "443", &hints, &res)
                             : getaddrinfo(host.UTF8String, "443", &hints, &res);
    if (r == 0 && res) {
        for (struct addrinfo *p = res; p; p = p->ai_next) {
            NSString *s = DSAddrString(p->ai_addr);
            if (s && ![out containsObject:s]) [out addObject:s];
        }
        freeaddrinfo(res);
    }
    if (out.count == 0) {   // احتياطي: محلّل 8.8.8.8 المدمج
        struct in_addr ips[8]; int n = 0;
        if (DSResolve4(host.UTF8String, ips, 8, &n)) {
            for (int i = 0; i < n; i++) {
                char b[INET_ADDRSTRLEN];
                if (inet_ntop(AF_INET, &ips[i], b, sizeof b)) {
                    NSString *s = @(b);
                    if (![out containsObject:s]) [out addObject:s];
                }
            }
        }
    }
    if (msOut) *msOut = (ASNow() - t0) * 1000.0;
    return out;
}

static NSArray<NSNumber *> *ASPortsForEntry(NSDictionary *e) {
    NSMutableArray *ports = [NSMutableArray array];
    BOOL isIP = [e[@"type"] isEqualToString:@"ip"];
    for (NSString *s in e[@"src"]) {
        if (![s isKindOfClass:NSString.class]) continue;
        NSRange r = [s rangeOfString:@":" options:NSBackwardsSearch];
        if (r.location == NSNotFound) continue;
        NSInteger p = [[s substringFromIndex:r.location + 1] integerValue];
        if (p > 0 && p <= 65535 && ![ports containsObject:@(p)]) [ports addObject:@(p)];
        if (ports.count >= 3) break;
    }
    if (ports.count == 0) {
        [ports addObject:@443];
        [ports addObject:@80];
    } else if (!isIP) {
        for (NSNumber *p in @[@443, @80]) {
            if (ports.count >= 3) break;
            if (![ports containsObject:p]) [ports addObject:p];
        }
    }
    return ports;
}

// اختبار TCP مباشر (يتجاوز hook connect حتى لا يتحول الهدف إلى 8.8.8.8)
static int ASTCPProbe(NSString *ip, int port, int timeoutMs, double *msOut) {
    if (ip.length == 0 || port <= 0 || port > 65535) return -1;
    BOOL v6 = [ip containsString:@":"];
    int fd = socket(v6 ? AF_INET6 : AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return -1;
    int flags = fcntl(fd, F_GETFL, 0);
    if (flags >= 0) fcntl(fd, F_SETFL, flags | O_NONBLOCK);

    double t0 = ASNow();
    int r = -1;
    if (v6) {
        struct sockaddr_in6 sa; memset(&sa, 0, sizeof sa);
        sa.sin6_len = sizeof sa; sa.sin6_family = AF_INET6; sa.sin6_port = htons((uint16_t)port);
        if (inet_pton(AF_INET6, ip.UTF8String, &sa.sin6_addr) != 1) { close(fd); return -1; }
        r = (orig_connect ? orig_connect : connect)(fd, (struct sockaddr *)&sa, sizeof sa);
    } else {
        struct sockaddr_in sa; memset(&sa, 0, sizeof sa);
        sa.sin_len = sizeof sa; sa.sin_family = AF_INET; sa.sin_port = htons((uint16_t)port);
        if (inet_pton(AF_INET, ip.UTF8String, &sa.sin_addr) != 1) { close(fd); return -1; }
        r = (orig_connect ? orig_connect : connect)(fd, (struct sockaddr *)&sa, sizeof sa);
    }

    BOOL ok = NO;
    if (r == 0) ok = YES;
    else if (errno == EINPROGRESS) {
        fd_set wfds; FD_ZERO(&wfds); FD_SET(fd, &wfds);
        struct timeval tv; tv.tv_sec = timeoutMs / 1000; tv.tv_usec = (timeoutMs % 1000) * 1000;
        r = select(fd + 1, NULL, &wfds, NULL, &tv);
        if (r > 0) {
            int err = 0; socklen_t len = sizeof err;
            if (getsockopt(fd, SOL_SOCKET, SO_ERROR, &err, &len) == 0 && err == 0) ok = YES;
        }
    }
    if (msOut) *msOut = (ASNow() - t0) * 1000.0;
    close(fd);
    return ok ? 0 : -1;
}

typedef void (^ASProbeDone)(NSDictionary *result);

// يفحص هدفاً واحداً: DNS + TCP على المنافذ التي رُصدت (أو 443/80).
static void ASProbeEntry(NSDictionary *e, ASProbeDone done) {
    NSString *value = e[@"value"];
    BOOL isIP = [e[@"type"] isEqualToString:@"ip"];
    NSArray<NSNumber *> *ports = ASPortsForEntry(e);
    NSMutableArray<NSString *> *candidates = [NSMutableArray array];
    double dnsMs = 0;

    if (isIP) {
        if (ASIsPublicIP(value)) [candidates addObject:value];
    } else {
        for (NSString *ip in ASResolveHost(value, &dnsMs))
            if (ASIsPublicIP(ip) && ![candidates containsObject:ip]) [candidates addObject:ip];
        for (NSString *r in e[@"related"])
            if ([r isKindOfClass:NSString.class] && ASIsPublicIP(r) && ![candidates containsObject:r])
                [candidates addObject:r];
    }

    int bestMs = INT_MAX; NSString *bestIP = nil; int bestPort = 0;
    NSInteger tested = 0, okCount = 0;
    for (NSString *ip in candidates) {
        if (tested >= 3) break;
        tested++;
        for (NSNumber *pn in ports) {
            int port = pn.intValue;
            double ms = 0;
            if (ASTCPProbe(ip, port, 1200, &ms) == 0) {
                okCount++;
                if (ms < bestMs) { bestMs = (int)ms; bestIP = ip; bestPort = port; }
            }
        }
    }

    NSMutableDictionary *out = [NSMutableDictionary dictionary];
    out[@"when"] = @([[NSDate date] timeIntervalSince1970]);
    out[@"dnsMs"] = @((NSInteger)dnsMs);
    out[@"tested"] = @(tested);
    if (bestMs != INT_MAX) {
        out[@"status"] = @"OK";
        out[@"ms"] = @(bestMs);
        out[@"ip"] = bestIP ?: @"";
        out[@"port"] = @(bestPort);
        out[@"detail"] = [NSString stringWithFormat:@"%ld/%ld", (long)okCount, (long)(tested * ports.count)];
    } else if (candidates.count == 0) {
        out[@"status"] = isIP ? @"SKIP" : @"FAIL";
        out[@"ms"] = @0;
        out[@"detail"] = isIP ? @"عنوان محلي/غير عام" : @"فشل DNS";
    } else {
        out[@"status"] = @"FAIL";
        out[@"ms"] = @0;
        out[@"detail"] = @"لا يوجد اتصال TCP";
    }
    if (done) done(out);
}

@interface ASTestManager : NSObject
+ (instancetype)shared;
@property (nonatomic) ASTestMode mode;
@property (nonatomic) NSInteger intervalSec;
@property (atomic) BOOL running;
@property (atomic, strong) NSDate *lastRun;
@property (atomic) NSInteger lastTested, lastFailed;
- (void)start;
- (void)stop;
- (void)runNowForce:(BOOL)force;
- (NSArray<NSDictionary *> *)targetsForMode:(ASTestMode)mode force:(BOOL)force;
- (BOOL)entryMatches:(NSDictionary *)e mode:(ASTestMode)mode;
- (NSString *)modeTitle;
@end

@implementation ASTestManager {
    NSTimer *_timer;
}

+ (instancetype)shared {
    static ASTestManager *s; static dispatch_once_t once;
    dispatch_once(&once, ^{ s = [ASTestManager new]; });
    return s;
}

- (instancetype)init {
    if ((self = [super init])) {
        _mode = ASTestModeOff;
        _intervalSec = 120;
        NSData *d = [NSData dataWithContentsOfFile:[ASDir() stringByAppendingPathComponent:@"auto-test.json"]];
        if (d) {
            NSDictionary *j = [NSJSONSerialization JSONObjectWithData:d options:0 error:nil];
            if ([j isKindOfClass:NSDictionary.class]) {
                _mode = (ASTestMode)[j[@"mode"] integerValue];
                if (j[@"intervalSec"]) _intervalSec = MAX(30, [j[@"intervalSec"] integerValue]);
            }
        }
        [[NSNotificationCenter defaultCenter] addObserver:self selector:@selector(appActive)
            name:UIApplicationDidBecomeActiveNotification object:nil];
        [[NSNotificationCenter defaultCenter] addObserver:self selector:@selector(appResign)
            name:UIApplicationWillResignActiveNotification object:nil];
    }
    return self;
}

- (void)dealloc {
    [[NSNotificationCenter defaultCenter] removeObserver:self];
    [_timer invalidate];
}

- (void)save {
    NSDictionary *j = @{ @"mode": @(self.mode), @"intervalSec": @(self.intervalSec) };
    NSData *d = [NSJSONSerialization dataWithJSONObject:j options:NSJSONWritingPrettyPrinted error:nil];
    [d writeToFile:[ASDir() stringByAppendingPathComponent:@"auto-test.json"] atomically:YES];
}

- (void)setMode:(ASTestMode)mode {
    if (mode < ASTestModeOff || mode > ASTestModeChat) mode = ASTestModeOff;
    BOOL changed = (_mode != mode);
    _mode = mode;
    [self save];
    [self refreshTimer];
    if (changed && mode != ASTestModeOff) [self runNowForce:NO];
}

- (void)setIntervalSec:(NSInteger)intervalSec {
    if (intervalSec < 30) intervalSec = 30;
    _intervalSec = intervalSec;
    [self save];
    [self refreshTimer];
}

- (NSString *)modeTitle {
    switch (self.mode) {
        case ASTestModeAll: return @"ALL";
        case ASTestModeChat: return @"CHAT";
        default: return @"OFF";
    }
}

- (BOOL)entryMatches:(NSDictionary *)e mode:(ASTestMode)mode {
    NSString *type = e[@"type"], *value = e[@"value"];
    if (![type isKindOfClass:NSString.class] || ![value isKindOfClass:NSString.class]) return NO;
    if ([value.lowercaseString hasSuffix:@"nextdns.io"]) return NO;
    if (mode == ASTestModeAll) return YES;
    if (mode != ASTestModeChat) return NO;

    if ([type isEqualToString:@"domain"]) return DSIsChatHost(value.UTF8String);
    if ([type isEqualToString:@"ip"]) {
        @synchronized (DSChatIPs()) { if ([DSChatIPs() containsObject:value]) return YES; }
        for (NSString *r in e[@"related"])
            if ([r isKindOfClass:NSString.class] && DSIsChatHost(r.UTF8String)) return YES;
        for (NSString *s in e[@"src"])
            if ([s isKindOfClass:NSString.class] && [s.lowercaseString containsString:@"chat"]) return YES;
    }
    return NO;
}

- (NSArray<NSDictionary *> *)targetsForMode:(ASTestMode)mode force:(BOOL)force {
    if (mode == ASTestModeOff) return @[];
    NSArray *all = [[DSStore shared] snapshot];
    NSMutableArray *out = [NSMutableArray array];
    double now = [[NSDate date] timeIntervalSince1970];
    double cooldown = MAX(60.0, self.intervalSec * 0.8);
    for (NSDictionary *e in all) {
        if (![self entryMatches:e mode:mode]) continue;
        if (!force) {
            NSDictionary *p = e[@"probe"];
            double when = [p[@"when"] doubleValue];
            if (when > 0 && now - when < cooldown) continue;
        }
        [out addObject:e];
    }
    [out sortUsingComparator:^NSComparisonResult(NSDictionary *a, NSDictionary *b) {
        double ta = [a[@"probe"][@"when"] doubleValue];
        double tb = [b[@"probe"][@"when"] doubleValue];
        if (ta < tb) return NSOrderedAscending;
        if (ta > tb) return NSOrderedDescending;
        return NSOrderedSame;
    }];
    if (out.count > 120) [out removeObjectsInRange:NSMakeRange(120, out.count - 120)];
    return out;
}

- (void)postLog:(NSString *)line {
    [[NSNotificationCenter defaultCenter] postNotificationName:ASTestLogNotification object:line];
}

- (void)runNowForce:(BOOL)force {
    if (self.running) return;
    if (self.mode == ASTestModeOff && !force) return;
    ASTestMode mode = self.mode;
    if (mode == ASTestModeOff) mode = ASTestModeAll;   // TEST NOW بدون وضع: اختبر الكل
    self.running = YES;

    dispatch_async(dispatch_get_global_queue(DISPATCH_QUEUE_PRIORITY_DEFAULT, 0), ^{
        NSArray *targets = [self targetsForMode:mode force:force];
        if (targets.count == 0) {
            dispatch_async(dispatch_get_main_queue(), ^{
                self.running = NO;
                [self postLog:@"لا توجد أهداف جديدة للاختبار — شغّل التطبيق/اللعبة وانتظر التقاط الاتصالات."];
                [[NSNotificationCenter defaultCenter] postNotificationName:ASTestDidUpdateNotification object:nil];
            });
            return;
        }

        [self postLog:[NSString stringWithFormat:@"🔎 بدء اختبار %lu هدف — الوضع: %@", (unsigned long)targets.count, mode == ASTestModeChat ? @"CHAT" : @"ALL"]];
        dispatch_semaphore_t sem = dispatch_semaphore_create(6);
        dispatch_group_t group = dispatch_group_create();
        __block NSInteger tested = 0, failed = 0;

        for (NSDictionary *e in targets) {
            dispatch_group_enter(group);
            dispatch_async(dispatch_get_global_queue(DISPATCH_QUEUE_PRIORITY_DEFAULT, 0), ^{
                dispatch_semaphore_wait(sem, DISPATCH_TIME_FOREVER);
                __block NSDictionary *probe = nil;
                ASProbeEntry(e, ^(NSDictionary *r) { probe = r; });
                dispatch_semaphore_signal(sem);

                if (probe) {
                    [[DSStore shared] setProbe:probe forValue:e[@"value"]];
                    BOOL ok = [probe[@"status"] isEqualToString:@"OK"];
                    @synchronized (self) {
                        tested++;
                        if (!ok) failed++;
                    }
                    [self postLog:[NSString stringWithFormat:@"%@ %@ → %@ %@ms %@",
                        ok ? @"✅" : @"⚠️", e[@"value"], probe[@"status"] ?: @"?", probe[@"ms"] ?: @0,
                        probe[@"detail"] ?: @""]];
                    [[NSNotificationCenter defaultCenter] postNotificationName:ASTestDidUpdateNotification object:nil];
                }
                dispatch_group_leave(group);
            });
        }

        dispatch_group_wait(group, DISPATCH_TIME_FOREVER);
        dispatch_async(dispatch_get_main_queue(), ^{
            self.running = NO;
            self.lastRun = [NSDate date];
            self.lastTested = tested;
            self.lastFailed = failed;
            [self postLog:[NSString stringWithFormat:@"=== انتهى الاختبار: %ld ناجح / %ld فاشل ===",
                (long)(tested - failed), (long)failed]];
            [[NSNotificationCenter defaultCenter] postNotificationName:ASTestDidUpdateNotification object:nil];
        });
    });
}

- (void)refreshTimer {
    [_timer invalidate]; _timer = nil;
    if (self.mode == ASTestModeOff) return;
    if ([UIApplication sharedApplication].applicationState != UIApplicationStateActive) return;
    NSTimeInterval t = MAX(30, self.intervalSec);
    __weak typeof(self) weakSelf = self;
    _timer = [NSTimer scheduledTimerWithTimeInterval:t repeats:YES block:^(NSTimer *timer) {
        [weakSelf runNowForce:NO];
    }];
}

- (void)start {
    [self refreshTimer];
    if (self.mode != ASTestModeOff) [self runNowForce:NO];
}

- (void)stop {
    [_timer invalidate]; _timer = nil;
}

- (void)appActive {
    [self refreshTimer];
    if (self.mode == ASTestModeOff) return;
    if (!self.lastRun || -[self.lastRun timeIntervalSinceNow] > self.intervalSec) [self runNowForce:NO];
}

- (void)appResign {
    [_timer invalidate]; _timer = nil;
}

@end

#pragma mark - ServerTester engine (load test)

static NSString *STDir(void) { return ASDir(); }

@interface STSettings : NSObject
@property (atomic, copy) NSString *wsURL;
@property (atomic, copy) NSString *httpURL;
@property (atomic) NSInteger clients;
@property (atomic) NSInteger durationSec;
@property (atomic) NSInteger rateHz;
@property (atomic) NSInteger rampMs;
@property (atomic) BOOL autoOn;
@property (atomic) NSInteger autoIntervalMin;
+ (instancetype)shared;
- (void)save;
@end

@implementation STSettings
+ (instancetype)shared {
    static STSettings *s; static dispatch_once_t once;
    dispatch_once(&once, ^{
        s = [STSettings new];
        s.wsURL = @"ws://your-server.example.com:3000";
        s.httpURL = @"http://your-server.example.com:3000/health";
        s.clients = 10; s.durationSec = 15; s.rateHz = 5; s.rampMs = 50;
        s.autoOn = NO; s.autoIntervalMin = 30;
        NSString *p = [STDir() stringByAppendingPathComponent:@"server-test.json"];
        NSData *d = [NSData dataWithContentsOfFile:p];
        if (d) {
            NSDictionary *j = [NSJSONSerialization JSONObjectWithData:d options:0 error:nil];
            if ([j isKindOfClass:[NSDictionary class]]) {
                if (j[@"wsURL"]) s.wsURL = j[@"wsURL"];
                if (j[@"httpURL"]) s.httpURL = j[@"httpURL"];
                if (j[@"clients"]) s.clients = [j[@"clients"] integerValue];
                if (j[@"durationSec"]) s.durationSec = [j[@"durationSec"] integerValue];
                if (j[@"rateHz"]) s.rateHz = [j[@"rateHz"] integerValue];
                if (j[@"rampMs"]) s.rampMs = [j[@"rampMs"] integerValue];
                s.autoOn = [j[@"autoOn"] boolValue];
                if (j[@"autoIntervalMin"]) s.autoIntervalMin = [j[@"autoIntervalMin"] integerValue];
            }
        }
    });
    return s;
}
- (void)save {
    NSDictionary *j = @{ @"wsURL": self.wsURL ?: @"", @"httpURL": self.httpURL ?: @"",
        @"clients": @(self.clients), @"durationSec": @(self.durationSec), @"rateHz": @(self.rateHz),
        @"rampMs": @(self.rampMs), @"autoOn": @(self.autoOn), @"autoIntervalMin": @(self.autoIntervalMin) };
    NSData *d = [NSJSONSerialization dataWithJSONObject:j options:NSJSONWritingPrettyPrinted error:nil];
    [d writeToFile:[STDir() stringByAppendingPathComponent:@"server-test.json"] atomically:YES];
}
@end

@interface STStats : NSObject
@property (atomic) NSInteger connected, failed, closedEarly, sent, received, errors;
@property (atomic, strong) NSMutableArray<NSNumber *> *latencies;
@property (atomic, strong) NSMutableArray<NSNumber *> *connectTimes;
@end
@implementation STStats
- (instancetype)init { self = [super init]; if (self) { _latencies = [NSMutableArray array]; _connectTimes = [NSMutableArray array]; } return self; }
@end

typedef void (^STLogBlock)(NSString *line);
typedef void (^STDoneBlock)(STStats *stats);

@interface STRunner : NSObject
+ (void)runWithLog:(STLogBlock)log done:(STDoneBlock)done;
@end

@implementation STRunner

+ (double)avg:(NSArray<NSNumber *> *)a {
    if (!a.count) return 0;
    double s = 0; for (NSNumber *n in a) s += n.doubleValue;
    return s / a.count;
}
+ (double)pct:(NSArray<NSNumber *> *)a p:(double)p {
    if (!a.count) return 0;
    NSArray *sorted = [a sortedArrayUsingSelector:@selector(compare:)];
    NSInteger idx = MIN(sorted.count - 1, (NSInteger)((p/100.0) * sorted.count));
    return [sorted[idx] doubleValue];
}

+ (void)testHTTPWithLog:(STLogBlock)log stats:(STStats *)stats done:(dispatch_block_t)done {
    NSString *urlStr = [STSettings shared].httpURL;
    if (!urlStr.length) { done(); return; }
    log([NSString stringWithFormat:@"[HTTP] فحص %@", urlStr]);
    NSURL *url = [NSURL URLWithString:urlStr];
    if (!url) { log(@"  رابط HTTP غير صالح"); done(); return; }
    __block NSInteger remaining = 10, ok = 0;
    NSMutableArray<NSNumber *> *times = [NSMutableArray array];
    dispatch_queue_t q = dispatch_get_global_queue(DISPATCH_QUEUE_PRIORITY_DEFAULT, 0);
    void (^finishIfDone)(void) = ^{
        if (remaining == 0) {
            log([NSString stringWithFormat:@"  نجح %ld/10 | متوسط الزمن %.1fms", (long)ok, [self avg:times]]);
            done();
        }
    };
    for (int i = 0; i < 10; i++) {
        dispatch_async(q, ^{
            NSDate *t0 = [NSDate date];
            NSURLSessionDataTask *task = [[NSURLSession sharedSession] dataTaskWithURL:url
                completionHandler:^(NSData *data, NSURLResponse *response, NSError *error) {
                    @synchronized (stats) {
                        remaining--;
                        NSInteger ms = (NSInteger)([[NSDate date] timeIntervalSinceDate:t0] * 1000);
                        [times addObject:@(ms)];
                        NSHTTPURLResponse *http = (NSHTTPURLResponse *)response;
                        if (!error && http.statusCode >= 200 && http.statusCode < 400) ok++;
                        finishIfDone();
                    }
                }];
            [task resume];
        });
    }
}

+ (void)spawnClient:(NSInteger)clientId endAt:(NSDate *)endAt stats:(STStats *)stats group:(dispatch_group_t)group {
    dispatch_group_enter(group);
    NSURL *url = [NSURL URLWithString:[STSettings shared].wsURL];
    if (!url) { @synchronized (stats) { stats.failed++; } dispatch_group_leave(group); return; }
    NSURLSession *session = [NSURLSession sessionWithConfiguration:[NSURLSessionConfiguration defaultSessionConfiguration]];
    NSURLSessionWebSocketTask *ws = [session webSocketTaskWithURL:url];
    NSDate *connectStart = [NSDate date];
    __block BOOL opened = NO;
    __block NSInteger seq = 0;
    NSMutableDictionary<NSNumber *, NSDate *> *pending = [NSMutableDictionary dictionary];
    __block dispatch_source_t timer = nil;

    void (^finish)(void) = ^{
        if (timer) { dispatch_source_cancel(timer); timer = nil; }
        [ws cancelWithCloseCode:NSURLSessionWebSocketCloseCodeNormalClosure reason:nil];
        dispatch_group_leave(group);
    };

    __block void (^receiveLoop)(void);
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Warc-retain-cycles"
    receiveLoop = ^{
        [ws receiveMessageWithCompletionHandler:^(NSURLSessionWebSocketMessage *message, NSError *error) {
            if (error) { receiveLoop = nil; return; }
            @synchronized (stats) {
                stats.received++;
                NSString *text = message.string;
                NSNumber *matchedSeq = nil;
                if (text) {
                    NSData *d = [text dataUsingEncoding:NSUTF8StringEncoding];
                    NSDictionary *j = [NSJSONSerialization JSONObjectWithData:d options:0 error:nil];
                    if ([j isKindOfClass:[NSDictionary class]] && j[@"seq"]) matchedSeq = j[@"seq"];
                }
                @synchronized (pending) {
                    NSDate *sentAt = matchedSeq ? pending[matchedSeq] : pending.allValues.firstObject;
                    NSNumber *key = matchedSeq ?: pending.allKeys.firstObject;
                    if (sentAt) {
                        [stats.latencies addObject:@((NSInteger)([[NSDate date] timeIntervalSinceDate:sentAt] * 1000))];
                        [pending removeObjectForKey:key];
                    }
                }
            }
            if ([NSDate date].timeIntervalSince1970 < endAt.timeIntervalSince1970) receiveLoop();
            else receiveLoop = nil;   // كسر دورة الاحتفاظ عند انتهاء الحلقة
        }];
    };
#pragma clang diagnostic pop

    [ws resume];
    [ws sendPingWithPongReceiveHandler:^(NSError *error) {
        if (error) {
            @synchronized (stats) { if (!opened) stats.failed++; stats.errors++; }
            finish(); return;
        }
        opened = YES;
        @synchronized (stats) { stats.connected++; [stats.connectTimes addObject:@((NSInteger)([[NSDate date] timeIntervalSinceDate:connectStart]*1000))]; }
        receiveLoop();
        double interval = 1.0 / MAX(1, [STSettings shared].rateHz);
        timer = dispatch_source_create(DISPATCH_SOURCE_TYPE_TIMER, 0, 0, dispatch_get_global_queue(0,0));
        dispatch_source_set_timer(timer, dispatch_time(DISPATCH_TIME_NOW, (int64_t)(interval*NSEC_PER_SEC)), (uint64_t)(interval*NSEC_PER_SEC), (uint64_t)(interval*NSEC_PER_SEC*0.2));
        dispatch_source_set_event_handler(timer, ^{
            if ([NSDate date].timeIntervalSince1970 >= endAt.timeIntervalSince1970) { finish(); return; }
            seq++;
            NSDictionary *msg = @{ @"type": @"ping", @"playerId": @(clientId), @"seq": @(seq), @"t": @((long long)([NSDate date].timeIntervalSince1970*1000)) };
            NSData *d = [NSJSONSerialization dataWithJSONObject:msg options:0 error:nil];
            NSString *text = [[NSString alloc] initWithData:d encoding:NSUTF8StringEncoding];
            @synchronized (pending) { pending[@(seq)] = [NSDate date]; }
            [ws sendMessage:[[NSURLSessionWebSocketMessage alloc] initWithString:text] completionHandler:^(NSError *sendErr) {
                if (!sendErr) @synchronized (stats) { stats.sent++; }
            }];
        });
        dispatch_resume(timer);
    }];

    dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)([endAt timeIntervalSinceNow] * NSEC_PER_SEC) + (int64_t)(1*NSEC_PER_SEC)), dispatch_get_main_queue(), ^{
        if (timer) finish();
    });
}

+ (void)runWithLog:(STLogBlock)log done:(STDoneBlock)done {
    STStats *stats = [STStats new];
    STSettings *st = [STSettings shared];
    log(@"=== Server Tester ===");
    log([NSString stringWithFormat:@"ws=%@ http=%@ clients=%ld duration=%lds rate=%ld/s", st.wsURL, st.httpURL, (long)st.clients, (long)st.durationSec, (long)st.rateHz]);

    [self testHTTPWithLog:log stats:stats done:^{
        log([NSString stringWithFormat:@"\n[WS] تشغيل %ld لاعب لمدة %lds ...", (long)st.clients, (long)st.durationSec]);
        NSDate *endAt = [NSDate dateWithTimeIntervalSinceNow:st.durationSec];
        dispatch_group_t group = dispatch_group_create();
        for (NSInteger i = 0; i < st.clients; i++) {
            [self spawnClient:i+1 endAt:endAt stats:stats group:group];
            [NSThread sleepForTimeInterval:st.rampMs / 1000.0];
        }
        dispatch_group_notify(group, dispatch_get_main_queue(), ^{
            NSInteger lost = MAX(0, stats.sent - stats.received);
            log(@"\n=========== النتيجة ===========");
            log([NSString stringWithFormat:@"اللاعبون المتصلون: %ld/%ld", (long)stats.connected, (long)st.clients]);
            log([NSString stringWithFormat:@"فشل الاتصال: %ld | انقطاع مبكر: %ld | أخطاء: %ld", (long)stats.failed, (long)stats.closedEarly, (long)stats.errors]);
            log([NSString stringWithFormat:@"رسائل مُرسلة/مستلمة: %ld / %ld (مفقودة ~%ld)", (long)stats.sent, (long)stats.received, (long)lost]);
            log([NSString stringWithFormat:@"زمن الاستجابة: متوسط %.0fms | p50 %.0fms | p95 %.0fms | p99 %.0fms",
                 [self avg:stats.latencies], [self pct:stats.latencies p:50], [self pct:stats.latencies p:95], [self pct:stats.latencies p:99]]);
            BOOL healthy = stats.failed == 0 && stats.closedEarly == 0 && [self pct:stats.latencies p:95] < 200;
            log(healthy ? @"\nالحكم: ✅ السيرفر بحالة جيدة" : @"\nالحكم: ⚠️ هناك مشاكل تحتاج مراجعة");
            done(stats);
        });
    }];
}
@end

// مجدول اختبار الضغط التلقائي من النسخة الأصلية — يعمل فقط والتطبيق مفتوح بالمقدمة.
@interface STAutoManager : NSObject
+ (instancetype)shared;
- (void)start;
- (void)refreshTimer;
@end

@implementation STAutoManager {
    NSTimer *_timer;
}

+ (instancetype)shared {
    static STAutoManager *s; static dispatch_once_t once;
    dispatch_once(&once, ^{ s = [STAutoManager new]; });
    return s;
}

- (instancetype)init {
    if ((self = [super init])) {
        [[NSNotificationCenter defaultCenter] addObserver:self selector:@selector(appActive)
            name:UIApplicationDidBecomeActiveNotification object:nil];
        [[NSNotificationCenter defaultCenter] addObserver:self selector:@selector(appResign)
            name:UIApplicationWillResignActiveNotification object:nil];
    }
    return self;
}

- (void)dealloc {
    [[NSNotificationCenter defaultCenter] removeObserver:self];
    [_timer invalidate];
}

- (void)refreshTimer {
    [_timer invalidate]; _timer = nil;
    if (![STSettings shared].autoOn) return;
    if ([UIApplication sharedApplication].applicationState != UIApplicationStateActive) return;
    NSTimeInterval interval = MAX(60, [STSettings shared].autoIntervalMin * 60.0);
    __weak typeof(self) weakSelf = self;
    _timer = [NSTimer scheduledTimerWithTimeInterval:interval repeats:YES block:^(NSTimer *timer) {
        [STRunner runWithLog:^(NSString *line) {
            [[NSNotificationCenter defaultCenter] postNotificationName:ASTestLogNotification object:line];
        } done:^(STStats *stats) {
            [[NSNotificationCenter defaultCenter] postNotificationName:ASTestLogNotification
                object:[NSString stringWithFormat:@"⏱️ AUTO LOAD: اتصال %ld/%ld — نجاح آلي ✅",
                    (long)stats.connected, (long)[STSettings shared].clients]];
        }];
        (void)weakSelf;
    }];
}

- (void)start { [self refreshTimer]; }

- (void)appActive { [self refreshTimer]; }
- (void)appResign { [_timer invalidate]; _timer = nil; }

@end

#pragma mark - UI theme (Aflatoon cyber-terminal)

enum { kBG = 0x07060D, kPanel = 0x120E1E, kLine = 0x2B2143, kGreen = 0x00F5A0, kCyan = 0x00D4FF,
       kRed = 0xFF3B5C, kAmber = 0xFFB800, kPurple = 0xB388FF, kText = 0xE6EDF3, kDim = 0x7A8899, kGold = 0xD4AF37 };

static inline UIColor *DSHex(uint32_t h) {
    return [UIColor colorWithRed:((h >> 16) & 0xFF) / 255.0 green:((h >> 8) & 0xFF) / 255.0 blue:(h & 0xFF) / 255.0 alpha:1];
}
static UIFont *DSMono(CGFloat s, UIFontWeight w) { return [UIFont monospacedSystemFontOfSize:s weight:w]; }
static void DSGlow(CALayer *l, UIColor *c, CGFloat r) {
    l.shadowColor = c.CGColor; l.shadowOpacity = 0.9; l.shadowRadius = r; l.shadowOffset = CGSizeZero;
}
static UIImage *DSIcon(NSString *name, CGFloat pt) {
    UIImageSymbolConfiguration *cfg = [UIImageSymbolConfiguration configurationWithPointSize:pt weight:UIImageSymbolWeightSemibold];
    return [UIImage systemImageNamed:name withConfiguration:cfg];
}

@interface DSGradView : UIView
@end
@implementation DSGradView
+ (Class)layerClass { return CAGradientLayer.class; }
@end

@interface DSPill : UILabel
@end
@implementation DSPill
- (void)drawTextInRect:(CGRect)r { [super drawTextInRect:UIEdgeInsetsInsetRect(r, UIEdgeInsetsMake(2, 7, 2, 7))]; }
- (CGSize)intrinsicContentSize { CGSize s = [super intrinsicContentSize]; return CGSizeMake(s.width + 14, s.height + 4); }
@end

static void DSStylePill(DSPill *p, NSString *t, UIColor *c) {
    p.text = t; p.font = DSMono(10, UIFontWeightBold); p.textColor = c; p.textAlignment = NSTextAlignmentCenter;
    p.backgroundColor = [c colorWithAlphaComponent:0.14];
    p.layer.cornerRadius = 5; p.layer.borderWidth = 0.5; p.layer.borderColor = [c colorWithAlphaComponent:0.7].CGColor;
    p.clipsToBounds = YES;
}

#pragma mark - Row cell

@interface DSCell : UITableViewCell
- (void)configure:(NSDictionary *)e sent:(BOOL)sent;
@end

@implementation DSCell {
    UIView *_card, *_bar; UILabel *_title, *_meta, *_rel, *_count; UIImageView *_icon; DSPill *_tag;
}

- (UILabel *)label:(UIFont *)f color:(UIColor *)c {
    UILabel *l = [UILabel new]; l.font = f; l.textColor = c; l.translatesAutoresizingMaskIntoConstraints = NO; return l;
}

- (instancetype)initWithStyle:(UITableViewCellStyle)style reuseIdentifier:(NSString *)rid {
    if ((self = [super initWithStyle:style reuseIdentifier:rid])) {
        self.backgroundColor = UIColor.clearColor; self.contentView.backgroundColor = UIColor.clearColor;
        self.selectionStyle = UITableViewCellSelectionStyleNone;
        _card = [UIView new]; _card.backgroundColor = DSHex(kPanel); _card.layer.cornerRadius = 10;
        _card.layer.borderWidth = 1; _card.layer.borderColor = DSHex(kLine).CGColor; _card.clipsToBounds = YES;
        _card.translatesAutoresizingMaskIntoConstraints = NO; [self.contentView addSubview:_card];
        _bar = [UIView new]; _bar.translatesAutoresizingMaskIntoConstraints = NO; [_card addSubview:_bar];
        _icon = [UIImageView new]; _icon.contentMode = UIViewContentModeCenter; _icon.translatesAutoresizingMaskIntoConstraints = NO;
        _title = [self label:DSMono(14, UIFontWeightSemibold) color:DSHex(kText)]; _title.lineBreakMode = NSLineBreakByTruncatingMiddle;
        _meta = [self label:DSMono(11, UIFontWeightRegular) color:DSHex(kDim)];
        _rel = [self label:DSMono(11, UIFontWeightRegular) color:DSHex(kCyan)]; _rel.numberOfLines = 2;
        _count = [self label:DSMono(13, UIFontWeightBold) color:DSHex(kGreen)];
        [_count setContentHuggingPriority:UILayoutPriorityRequired forAxis:UILayoutConstraintAxisHorizontal];
        [_count setContentCompressionResistancePriority:UILayoutPriorityRequired forAxis:UILayoutConstraintAxisHorizontal];
        _tag = [DSPill new]; _tag.translatesAutoresizingMaskIntoConstraints = NO;
        [_tag setContentCompressionResistancePriority:UILayoutPriorityRequired forAxis:UILayoutConstraintAxisHorizontal];
        for (UIView *v in @[_icon, _title, _meta, _rel, _count, _tag]) [_card addSubview:v];
        [NSLayoutConstraint activateConstraints:@[
            [_card.topAnchor constraintEqualToAnchor:self.contentView.topAnchor constant:4],
            [_card.bottomAnchor constraintEqualToAnchor:self.contentView.bottomAnchor constant:-4],
            [_card.leadingAnchor constraintEqualToAnchor:self.contentView.leadingAnchor constant:2],
            [_card.trailingAnchor constraintEqualToAnchor:self.contentView.trailingAnchor constant:-2],
            [_bar.leadingAnchor constraintEqualToAnchor:_card.leadingAnchor], [_bar.topAnchor constraintEqualToAnchor:_card.topAnchor],
            [_bar.bottomAnchor constraintEqualToAnchor:_card.bottomAnchor], [_bar.widthAnchor constraintEqualToConstant:3],
            [_icon.leadingAnchor constraintEqualToAnchor:_bar.trailingAnchor constant:10],
            [_icon.topAnchor constraintEqualToAnchor:_card.topAnchor constant:10],
            [_icon.widthAnchor constraintEqualToConstant:20], [_icon.heightAnchor constraintEqualToConstant:20],
            [_title.leadingAnchor constraintEqualToAnchor:_icon.trailingAnchor constant:6],
            [_title.topAnchor constraintEqualToAnchor:_card.topAnchor constant:10],
            [_title.trailingAnchor constraintLessThanOrEqualToAnchor:_count.leadingAnchor constant:-8],
            [_count.trailingAnchor constraintEqualToAnchor:_card.trailingAnchor constant:-12],
            [_count.topAnchor constraintEqualToAnchor:_card.topAnchor constant:10],
            [_tag.trailingAnchor constraintEqualToAnchor:_card.trailingAnchor constant:-12],
            [_tag.topAnchor constraintEqualToAnchor:_count.bottomAnchor constant:6],
            [_meta.leadingAnchor constraintEqualToAnchor:_title.leadingAnchor],
            [_meta.topAnchor constraintEqualToAnchor:_title.bottomAnchor constant:4],
            [_meta.trailingAnchor constraintLessThanOrEqualToAnchor:_tag.leadingAnchor constant:-8],
            [_rel.leadingAnchor constraintEqualToAnchor:_title.leadingAnchor],
            [_rel.topAnchor constraintEqualToAnchor:_meta.bottomAnchor constant:3],
            [_rel.trailingAnchor constraintEqualToAnchor:_tag.leadingAnchor constant:-8],
            [_rel.bottomAnchor constraintEqualToAnchor:_card.bottomAnchor constant:-10],
            [_tag.bottomAnchor constraintLessThanOrEqualToAnchor:_card.bottomAnchor constant:-8]]];
    }
    return self;
}

- (void)configure:(NSDictionary *)e sent:(BOOL)sent {
    NSString *st = e[@"status"]; BOOL isIP = [e[@"type"] isEqualToString:@"ip"];
    UIColor *c; NSString *tag;
    if (sent) { c = DSHex(kPurple); tag = @"DENYLISTED"; }
    else if ([st isEqualToString:@"BLOCKED"]) { c = DSHex(kRed); tag = @"BLOCKED"; }
    else if ([st isEqualToString:@"FAILED"]) { c = DSHex(kAmber); tag = @"FAILED"; }
    else { c = DSHex(kGreen); tag = @"LIVE"; }
    _bar.backgroundColor = c; DSStylePill(_tag, tag, c);
    _icon.image = DSIcon(isIP ? @"network" : @"globe", 15); _icon.tintColor = isIP ? DSHex(kAmber) : DSHex(kCyan);
    _title.text = e[@"value"];
    _count.text = [NSString stringWithFormat:@"×%@", e[@"count"]];
    _meta.text = [(NSArray *)e[@"src"] componentsJoinedByString:@" · "];
    NSArray *rel = e[@"related"];
    NSArray *shown = rel.count > 3 ? [rel subarrayWithRange:NSMakeRange(0, 3)] : rel;
    NSString *relText = shown.count ? [NSString stringWithFormat:@"→ %@%@", [shown componentsJoinedByString:@", "], rel.count > 3 ? @" …" : @""] : nil;
    NSDictionary *probe = e[@"probe"];
    if ([probe[@"status"] isKindOfClass:NSString.class]) {
        NSString *ps = probe[@"status"];
        NSString *line = [NSString stringWithFormat:@"🧪 %@ %@ms %@", ps, probe[@"ms"] ?: @0, probe[@"detail"] ?: @""];
        relText = relText.length ? [relText stringByAppendingFormat:@"\n%@", line] : line;
    }
    _rel.text = relText;
}
@end

#pragma mark - Rules screen

@interface DSRulesVC : UITableViewController
+ (void)promptFrom:(NSString *)from over:(UIViewController *)vc done:(void (^)(void))done;
@end

@implementation DSRulesVC

+ (void)promptFrom:(NSString *)from over:(UIViewController *)vc done:(void (^)(void))done {
    UIAlertController *a = [UIAlertController alertControllerWithTitle:@"🔁 استبدال"
        message:@"مثال: 1.1.1.1 ← 8.8.8.8\nأو *.example.com ← 1.2.3.4" preferredStyle:UIAlertControllerStyleAlert];
    NSArray *ph = @[@"من (نطاق أو IP)", @"إلى (IP أو نطاق)"];
    for (NSInteger i = 0; i < 2; i++) {
        [a addTextFieldWithConfigurationHandler:^(UITextField *t) {
            t.placeholder = ph[i]; t.text = i == 0 ? from : nil; t.font = DSMono(14, UIFontWeightRegular);
            t.autocapitalizationType = UITextAutocapitalizationTypeNone;
            t.autocorrectionType = UITextAutocorrectionTypeNo; t.keyboardType = UIKeyboardTypeURL;
        }];
    }
    __weak UIAlertController *wa = a;
    [a addAction:[UIAlertAction actionWithTitle:@"إلغاء" style:UIAlertActionStyleCancel handler:nil]];
    [a addAction:[UIAlertAction actionWithTitle:@"إضافة وتفعيل" style:UIAlertActionStyleDefault handler:^(UIAlertAction *x) {
        [[DSSettings shared] addRuleFrom:wa.textFields[0].text to:wa.textFields[1].text];
        if (done) done();
    }]];
    [vc presentViewController:a animated:YES completion:nil];
}

- (void)viewDidLoad {
    [super viewDidLoad];
    self.overrideUserInterfaceStyle = UIUserInterfaceStyleDark;
    self.title = @"RULES // قواعد الاستبدال";
    self.view.backgroundColor = DSHex(kBG);
    self.tableView.backgroundColor = DSHex(kBG);
    self.tableView.separatorColor = DSHex(kLine);
    self.navigationItem.leftBarButtonItem = [[UIBarButtonItem alloc] initWithBarButtonSystemItem:UIBarButtonSystemItemDone target:self action:@selector(done)];
    self.navigationItem.rightBarButtonItem = [[UIBarButtonItem alloc] initWithBarButtonSystemItem:UIBarButtonSystemItemAdd target:self action:@selector(add)];
}
- (void)viewWillAppear:(BOOL)animated {
    [super viewWillAppear:animated];
    UINavigationBar *nb = self.navigationController.navigationBar;
    nb.barStyle = UIBarStyleBlack; nb.tintColor = DSHex(kGreen); nb.barTintColor = DSHex(kBG); nb.translucent = NO;
    nb.titleTextAttributes = @{ NSForegroundColorAttributeName: DSHex(kGreen), NSFontAttributeName: DSMono(14, UIFontWeightBold) };
}
- (void)done { [self dismissViewControllerAnimated:YES completion:nil]; }
- (void)add { [DSRulesVC promptFrom:nil over:self done:^{ [self.tableView reloadData]; }]; }

- (NSInteger)tableView:(UITableView *)tv numberOfRowsInSection:(NSInteger)s {
    NSUInteger n = [DSSettings shared].rules.count;
    if (n == 0) {
        UILabel *l = [UILabel new]; l.text = @"$ no rules yet\nاضغط + لإضافة قاعدة استبدال"; l.numberOfLines = 0;
        l.textAlignment = NSTextAlignmentCenter; l.font = DSMono(13, UIFontWeightRegular); l.textColor = DSHex(kDim);
        tv.backgroundView = l;
    } else tv.backgroundView = nil;
    return n;
}
- (NSString *)tableView:(UITableView *)tv titleForFooterInSection:(NSInteger)s {
    return @"التفعيل يُحفظ تلقائياً ويبقى بعد الخروج من اللعبة. القاعدة تُطبَّق على الاتصالات الجديدة (قد تحتاج إعادة تشغيل اللعبة). يدعم *.domain.com";
}
- (void)tableView:(UITableView *)tv willDisplayFooterView:(UIView *)v forSection:(NSInteger)s {
    ((UITableViewHeaderFooterView *)v).textLabel.textColor = DSHex(kDim);
}
- (UITableViewCell *)tableView:(UITableView *)tv cellForRowAtIndexPath:(NSIndexPath *)ip {
    UITableViewCell *c = [[UITableViewCell alloc] initWithStyle:UITableViewCellStyleDefault reuseIdentifier:nil];
    NSDictionary *r = [DSSettings shared].rules[ip.row];
    c.backgroundColor = DSHex(kPanel);
    c.textLabel.text = [NSString stringWithFormat:@"%@\n   ↳ %@", r[@"from"], r[@"to"]];
    c.textLabel.font = DSMono(13, UIFontWeightMedium); c.textLabel.textColor = DSHex(kGreen); c.textLabel.numberOfLines = 3;
    UISwitch *sw = [UISwitch new]; sw.on = [r[@"enabled"] boolValue]; sw.tag = ip.row; sw.onTintColor = DSHex(kGreen);
    [sw addTarget:self action:@selector(toggled:) forControlEvents:UIControlEventValueChanged];
    c.accessoryView = sw;
    return c;
}
- (void)toggled:(UISwitch *)sw { [[DSSettings shared] setRule:sw.tag enabled:sw.isOn]; }
- (void)tableView:(UITableView *)tv commitEditingStyle:(UITableViewCellEditingStyle)st forRowAtIndexPath:(NSIndexPath *)ip {
    if (st != UITableViewCellEditingStyleDelete) return;
    [[DSSettings shared] removeRule:ip.row];
    [tv reloadData];
}
@end

#pragma mark - Server test screen (merged)

@interface DSTestVC : UIViewController <UITextFieldDelegate>
@end

@implementation DSTestVC {
    UILabel *_status, *_modeHint;
    UISegmentedControl *_modeSeg;
    UIButton *_intervalBtn, *_testNowBtn, *_copyBtn;
    UIButton *_wsBtn, *_httpBtn, *_clientsBtn, *_durationBtn, *_rateBtn, *_runBtn;
    UIButton *_autoLoadBtn, *_autoLoadIntervalBtn;
    UITextView *_log;
    BOOL _loadRunning;
    NSTimer *_refresh;
}

- (UIButton *)row:(NSString *)title value:(NSString *)value color:(UIColor *)c sel:(SEL)sel {
    UIButton *b = [UIButton buttonWithType:UIButtonTypeCustom];
    [b setTitle:[NSString stringWithFormat:@"%@: %@", title, value] forState:UIControlStateNormal];
    [b setTitleColor:c forState:UIControlStateNormal];
    b.titleLabel.font = DSMono(12, UIFontWeightSemibold);
    b.contentHorizontalAlignment = UIControlContentHorizontalAlignmentLeft;
    b.titleEdgeInsets = UIEdgeInsetsMake(0, 10, 0, 10);
    b.backgroundColor = [c colorWithAlphaComponent:0.08];
    b.layer.cornerRadius = 9; b.layer.borderWidth = 1; b.layer.borderColor = [c colorWithAlphaComponent:0.4].CGColor;
    [b.heightAnchor constraintEqualToConstant:38].active = YES;
    [b addTarget:self action:sel forControlEvents:UIControlEventTouchUpInside];
    return b;
}

- (UIButton *)action:(NSString *)title color:(UIColor *)c sel:(SEL)sel {
    UIButton *b = [UIButton buttonWithType:UIButtonTypeCustom];
    [b setTitle:title forState:UIControlStateNormal];
    [b setTitleColor:c forState:UIControlStateNormal];
    b.titleLabel.font = DSMono(12, UIFontWeightHeavy);
    b.backgroundColor = [c colorWithAlphaComponent:0.12];
    b.layer.cornerRadius = 10; b.layer.borderWidth = 1; b.layer.borderColor = c.CGColor;
    [b.heightAnchor constraintEqualToConstant:40].active = YES;
    [b addTarget:self action:sel forControlEvents:UIControlEventTouchUpInside];
    return b;
}

- (UILabel *)section:(NSString *)t {
    UILabel *l = [UILabel new];
    l.text = [NSString stringWithFormat:@"◆  %@  ◆", [t uppercaseString]]; l.textAlignment = NSTextAlignmentCenter;
    l.font = [UIFont systemFontOfSize:11 weight:UIFontWeightHeavy];
    l.textColor = DSHex(kGold); DSGlow(l.layer, DSHex(kGold), 5); l.layer.shadowOpacity = 0.5;
    return l;
}

- (void)viewDidLoad {
    [super viewDidLoad];
    self.overrideUserInterfaceStyle = UIUserInterfaceStyleDark;
    self.view.backgroundColor = DSHex(kBG);
    self.title = @"SERVER TEST";
    self.navigationItem.rightBarButtonItem = [[UIBarButtonItem alloc] initWithTitle:@"إغلاق"
        style:UIBarButtonItemStyleDone target:self action:@selector(closeTap)];

    UIScrollView *sv = [UIScrollView new]; sv.translatesAutoresizingMaskIntoConstraints = NO;
    sv.keyboardDismissMode = UIScrollViewKeyboardDismissModeOnDrag;
    [self.view addSubview:sv];

    UILabel *title = [UILabel new];
    title.text = @"⚡ SERVER TEST";
    title.font = DSMono(18, UIFontWeightHeavy);
    title.textColor = DSHex(kGreen);
    DSGlow(title.layer, DSHex(kGreen), 6);

    UILabel *credit = [UILabel new];
    credit.text = @"  ✦ أفلاطون • Aflatoon  ";
    credit.font = [UIFont systemFontOfSize:10.5 weight:UIFontWeightBold];
    credit.textColor = DSHex(kGold);
    credit.backgroundColor = [DSHex(kGold) colorWithAlphaComponent:0.12];
    credit.layer.cornerRadius = 8; credit.clipsToBounds = YES;
    credit.textAlignment = NSTextAlignmentCenter;

    UIStackView *header = [[UIStackView alloc] initWithArrangedSubviews:@[title, [UIView new], credit]];
    header.axis = UILayoutConstraintAxisHorizontal; header.alignment = UIStackViewAlignmentCenter;

    _status = [UILabel new];
    _status.font = DSMono(11, UIFontWeightRegular);
    _status.textColor = DSHex(kText);
    _status.numberOfLines = 0;
    _status.backgroundColor = DSHex(kPanel);
    _status.layer.cornerRadius = 10; _status.layer.borderWidth = 1;
    _status.layer.borderColor = DSHex(kLine).CGColor; _status.clipsToBounds = YES;
    _status.text = @"جاهز.";

    _modeSeg = [[UISegmentedControl alloc] initWithItems:@[@"OFF", @"ALL", @"CHAT"]];
    _modeSeg.selectedSegmentIndex = [ASTestManager shared].mode;
    _modeSeg.backgroundColor = DSHex(kPanel);
    _modeSeg.selectedSegmentTintColor = DSHex(kGreen);
    [_modeSeg setTitleTextAttributes:@{ NSForegroundColorAttributeName: DSHex(kDim), NSFontAttributeName: DSMono(11, UIFontWeightBold) } forState:UIControlStateNormal];
    [_modeSeg setTitleTextAttributes:@{ NSForegroundColorAttributeName: DSHex(kBG), NSFontAttributeName: DSMono(11, UIFontWeightHeavy) } forState:UIControlStateSelected];
    [_modeSeg addTarget:self action:@selector(modeChanged:) forControlEvents:UIControlEventValueChanged];

    _modeHint = [UILabel new];
    _modeHint.font = DSMono(10, UIFontWeightRegular);
    _modeHint.textColor = DSHex(kDim);
    _modeHint.numberOfLines = 0;
    _modeHint.text = @"ALL: كل النطاقات وIP/DNS · CHAT: IP/DNS الدردشة والكتابة أونلاين.\nالاختبار = DNS + اتصال TCP بالمنافذ المرصودة (أو 443/80) — تلقائي كل فترة.";

    _intervalBtn = [self action:@"AUTO: كل 120 ثانية" color:DSHex(kCyan) sel:@selector(intervalTap)];
    _testNowBtn = [self action:@"▶ اختبار الأهداف الآن" color:DSHex(kGreen) sel:@selector(testNowTap)];
    _copyBtn = [self action:@"📋 نسخ الأهداف" color:DSHex(kPurple) sel:@selector(copyTargetsTap)];

    STSettings *st = [STSettings shared];
    _wsBtn = [self row:@"WS" value:st.wsURL color:DSHex(kCyan) sel:@selector(editWS)];
    _httpBtn = [self row:@"HTTP" value:st.httpURL color:DSHex(kCyan) sel:@selector(editHTTP)];
    _clientsBtn = [self row:@"CLIENTS" value:[NSString stringWithFormat:@"%ld", (long)st.clients] color:DSHex(kAmber) sel:@selector(cycleClients)];
    _durationBtn = [self row:@"DURATION(s)" value:[NSString stringWithFormat:@"%ld", (long)st.durationSec] color:DSHex(kAmber) sel:@selector(cycleDuration)];
    _rateBtn = [self row:@"RATE(/s)" value:[NSString stringWithFormat:@"%ld", (long)st.rateHz] color:DSHex(kAmber) sel:@selector(cycleRate)];
    _runBtn = [self action:@"▶ RUN NOW" color:DSHex(kGreen) sel:@selector(runTap)];
    _autoLoadBtn = [self action:@"AUTO LOAD: OFF" color:DSHex(kCyan) sel:@selector(autoLoadTap)];
    _autoLoadIntervalBtn = [self action:@"كل 30 دقيقة" color:DSHex(kDim) sel:@selector(autoLoadIntervalTap)];
    [self refreshAutoLoadButtons];
    UIStackView *loadAutoRow = [[UIStackView alloc] initWithArrangedSubviews:@[_autoLoadBtn, _autoLoadIntervalBtn]];
    loadAutoRow.axis = UILayoutConstraintAxisHorizontal;
    loadAutoRow.distribution = UIStackViewDistributionFillEqually;
    loadAutoRow.spacing = 6;

    _log = [UITextView new];
    _log.backgroundColor = DSHex(kPanel); _log.textColor = DSHex(kText);
    _log.font = DSMono(10.5, UIFontWeightRegular);
    _log.layer.cornerRadius = 8; _log.editable = NO;
    _log.text = @"جاهز. اختر ALL أو CHAT ثم اضغط «اختبار الأهداف الآن»، أو استخدم RUN NOW لاختبار ضغط سيرفرك الخاص.";
    [_log.heightAnchor constraintEqualToConstant:230].active = YES;

    UILabel *foot = [UILabel new];
    foot.text = @"© Aflatoon // أفلاطون — all rights reserved";
    foot.textAlignment = NSTextAlignmentCenter;
    foot.font = DSMono(10, UIFontWeightMedium);
    foot.textColor = DSHex(kDim);

    UIStackView *main = [[UIStackView alloc] initWithArrangedSubviews:@[
        header, credit, _status,
        [self section:@"AUTO TEST — الأهداف الملتقطة"], _modeSeg, _modeHint, _intervalBtn, _testNowBtn, _copyBtn,
        [self section:@"LOAD TEST — سيرفرك الخاص"], _wsBtn, _httpBtn, _clientsBtn, _durationBtn, _rateBtn, _runBtn, loadAutoRow,
        [self section:@"LOG"], _log, foot]];
    main.axis = UILayoutConstraintAxisVertical; main.spacing = 8;
    main.translatesAutoresizingMaskIntoConstraints = NO;
    [sv addSubview:main];

    [NSLayoutConstraint activateConstraints:@[
        [sv.topAnchor constraintEqualToAnchor:self.view.safeAreaLayoutGuide.topAnchor],
        [sv.leadingAnchor constraintEqualToAnchor:self.view.leadingAnchor],
        [sv.trailingAnchor constraintEqualToAnchor:self.view.trailingAnchor],
        [sv.bottomAnchor constraintEqualToAnchor:self.view.bottomAnchor],
        [main.topAnchor constraintEqualToAnchor:sv.contentLayoutGuide.topAnchor constant:14],
        [main.bottomAnchor constraintEqualToAnchor:sv.contentLayoutGuide.bottomAnchor constant:-18],
        [main.leadingAnchor constraintEqualToAnchor:sv.contentLayoutGuide.leadingAnchor constant:14],
        [main.trailingAnchor constraintEqualToAnchor:sv.contentLayoutGuide.trailingAnchor constant:-14],
        [main.widthAnchor constraintEqualToAnchor:sv.frameLayoutGuide.widthAnchor constant:-28]]];

    [self refreshStatus];
}

- (void)viewWillAppear:(BOOL)animated {
    [super viewWillAppear:animated];
    UINavigationBar *nb = self.navigationController.navigationBar;
    nb.barStyle = UIBarStyleBlack; nb.tintColor = DSHex(kGreen); nb.barTintColor = DSHex(kBG); nb.translucent = NO;
    nb.titleTextAttributes = @{ NSForegroundColorAttributeName: DSHex(kGreen), NSFontAttributeName: DSMono(14, UIFontWeightBold) };
    [[NSNotificationCenter defaultCenter] addObserver:self selector:@selector(logNote:) name:ASTestLogNotification object:nil];
    [[NSNotificationCenter defaultCenter] addObserver:self selector:@selector(updateNote:) name:ASTestDidUpdateNotification object:nil];
    [_refresh invalidate];
    _refresh = [NSTimer scheduledTimerWithTimeInterval:2.0 target:self selector:@selector(refreshStatus) userInfo:nil repeats:YES];
    [self refreshStatus];
}

- (void)viewWillDisappear:(BOOL)animated {
    [super viewWillDisappear:animated];
    [[NSNotificationCenter defaultCenter] removeObserver:self];
    [_refresh invalidate]; _refresh = nil;
}

- (void)dealloc {
    [[NSNotificationCenter defaultCenter] removeObserver:self];
    [_refresh invalidate];
}

- (void)closeTap { [self dismissViewControllerAnimated:YES completion:nil]; }

- (void)logNote:(NSNotification *)n {
    NSString *line = [n.object isKindOfClass:NSString.class] ? n.object : nil;
    if (line) [self appendLog:line];
}

- (void)updateNote:(NSNotification *)n { [self refreshStatus]; }

- (void)refreshStatus {
    ASTestManager *m = [ASTestManager shared];
    NSArray *all = [[DSStore shared] snapshot];
    NSInteger allCount = 0, chatCount = 0, tested = 0, ok = 0;
    for (NSDictionary *e in all) {
        if ([m entryMatches:e mode:ASTestModeAll]) allCount++;
        if ([m entryMatches:e mode:ASTestModeChat]) chatCount++;
        NSDictionary *p = e[@"probe"];
        if ([p[@"status"] isKindOfClass:NSString.class]) {
            tested++;
            if ([p[@"status"] isEqualToString:@"OK"]) ok++;
        }
    }
    NSString *last = m.lastRun ? [NSDateFormatter localizedStringFromDate:m.lastRun
        dateStyle:NSDateFormatterNoStyle timeStyle:NSDateFormatterMediumStyle] : @"—";
    _status.text = [NSString stringWithFormat:@"  الأهداف الملتقطة: ALL %ld · CHAT %ld\n  تم اختبارها: %ld (ناجح %ld · فاشل/تخطي %ld)\n  آخر تشغيل: %@%@  ",
        (long)allCount, (long)chatCount, (long)tested, (long)ok, (long)(tested - ok), last,
        m.running ? @"   ⏳ جارٍ..." : @""];
    _modeSeg.selectedSegmentIndex = m.mode;
    [_intervalBtn setTitle:[NSString stringWithFormat:@"AUTO: كل %ld ثانية", (long)m.intervalSec] forState:UIControlStateNormal];
}

- (void)modeChanged:(UISegmentedControl *)seg {
    ASTestManager *m = [ASTestManager shared];
    m.mode = (ASTestMode)seg.selectedSegmentIndex;
    [self refreshStatus];
    [self appendLog:[NSString stringWithFormat:@"AUTO TEST: %@", [m modeTitle]]];
}

- (void)intervalTap {
    static NSArray *opts;
    if (!opts) opts = @[@30, @60, @120, @300, @600];
    ASTestManager *m = [ASTestManager shared];
    NSInteger idx = [opts indexOfObject:@(m.intervalSec)];
    idx = (idx == NSNotFound) ? 0 : (idx + 1) % opts.count;
    m.intervalSec = [opts[idx] integerValue];
    [self refreshStatus];
}

- (void)testNowTap {
    ASTestManager *m = [ASTestManager shared];
    if (m.mode == ASTestModeOff) {
        m.mode = ASTestModeAll;
        _modeSeg.selectedSegmentIndex = ASTestModeAll;
    }
    [m runNowForce:YES];
    [self appendLog:@"▶ بدء الاختبار اليدوي للأهداف الملتقطة..."];
}

- (void)copyTargetsTap {
    ASTestManager *m = [ASTestManager shared];
    ASTestMode mode = m.mode == ASTestModeOff ? ASTestModeAll : m.mode;
    NSArray *targets = [m targetsForMode:mode force:YES];
    NSMutableString *s = [NSMutableString string];
    for (NSDictionary *e in targets) {
        NSDictionary *p = e[@"probe"];
        [s appendFormat:@"%@\t%@\t%@\t%@ms\n", e[@"type"], e[@"value"],
            p[@"status"] ?: @"UNTESTED", p[@"ms"] ?: @0];
    }
    UIPasteboard.generalPasteboard.string = s;
    [self appendLog:[NSString stringWithFormat:@"📋 نُسخ %lu هدف إلى الحافظة", (unsigned long)targets.count]];
}

- (void)appendLog:(NSString *)line {
    dispatch_async(dispatch_get_main_queue(), ^{
        if (!self->_log) return;
        self->_log.text = [self->_log.text stringByAppendingFormat:@"\n%@", line];
        [self->_log scrollRangeToVisible:NSMakeRange(self->_log.text.length, 0)];
    });
}

- (void)promptForKey:(NSString *)key title:(NSString *)title current:(NSString *)current {
    UIAlertController *ac = [UIAlertController alertControllerWithTitle:title message:nil preferredStyle:UIAlertControllerStyleAlert];
    [ac addTextFieldWithConfigurationHandler:^(UITextField *tf) {
        tf.text = current;
        tf.autocapitalizationType = UITextAutocapitalizationTypeNone;
        tf.autocorrectionType = UITextAutocorrectionTypeNo;
        tf.keyboardType = UIKeyboardTypeURL;
    }];
    __weak typeof(self) weakSelf = self;
    [ac addAction:[UIAlertAction actionWithTitle:@"حفظ" style:UIAlertActionStyleDefault handler:^(UIAlertAction *a) {
        NSString *val = [ac.textFields.firstObject.text stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceAndNewlineCharacterSet];
        STSettings *st = [STSettings shared];
        __strong typeof(weakSelf) strongSelf = weakSelf;
        if ([key isEqualToString:@"ws"]) {
            st.wsURL = val;
            if (strongSelf) [strongSelf->_wsBtn setTitle:[NSString stringWithFormat:@"WS: %@", val] forState:UIControlStateNormal];
        } else {
            st.httpURL = val;
            if (strongSelf) [strongSelf->_httpBtn setTitle:[NSString stringWithFormat:@"HTTP: %@", val] forState:UIControlStateNormal];
        }
        [st save];
    }]];
    [ac addAction:[UIAlertAction actionWithTitle:@"إلغاء" style:UIAlertActionStyleCancel handler:nil]];
    [self presentViewController:ac animated:YES completion:nil];
}

- (void)editWS { [self promptForKey:@"ws" title:@"عنوان WebSocket (ws:// أو wss://)" current:[STSettings shared].wsURL]; }
- (void)editHTTP { [self promptForKey:@"http" title:@"عنوان فحص HTTP (اختياري)" current:[STSettings shared].httpURL]; }

- (void)cycleClients {
    static NSArray *opts; if (!opts) opts = @[@5, @10, @25, @50, @100];
    STSettings *st = [STSettings shared];
    NSInteger idx = [opts indexOfObject:@(st.clients)]; idx = (idx == NSNotFound) ? 0 : (idx + 1) % opts.count;
    st.clients = [opts[idx] integerValue]; [st save];
    [_clientsBtn setTitle:[NSString stringWithFormat:@"CLIENTS: %ld", (long)st.clients] forState:UIControlStateNormal];
}
- (void)cycleDuration {
    static NSArray *opts; if (!opts) opts = @[@10, @15, @30, @60, @120];
    STSettings *st = [STSettings shared];
    NSInteger idx = [opts indexOfObject:@(st.durationSec)]; idx = (idx == NSNotFound) ? 0 : (idx + 1) % opts.count;
    st.durationSec = [opts[idx] integerValue]; [st save];
    [_durationBtn setTitle:[NSString stringWithFormat:@"DURATION(s): %ld", (long)st.durationSec] forState:UIControlStateNormal];
}
- (void)cycleRate {
    static NSArray *opts; if (!opts) opts = @[@1, @2, @5, @10, @20];
    STSettings *st = [STSettings shared];
    NSInteger idx = [opts indexOfObject:@(st.rateHz)]; idx = (idx == NSNotFound) ? 0 : (idx + 1) % opts.count;
    st.rateHz = [opts[idx] integerValue]; [st save];
    [_rateBtn setTitle:[NSString stringWithFormat:@"RATE(/s): %ld", (long)st.rateHz] forState:UIControlStateNormal];
}

- (void)runTap {
    if (_loadRunning) return;
    _loadRunning = YES;
    _log.text = @"";
    [_runBtn setTitle:@"⏳ جارٍ الاختبار..." forState:UIControlStateNormal];
    __weak typeof(self) weakSelf = self;
    [STRunner runWithLog:^(NSString *line) { [weakSelf appendLog:line]; } done:^(STStats *stats) {
        __strong typeof(weakSelf) strongSelf = weakSelf;
        if (!strongSelf) return;
        strongSelf->_loadRunning = NO;
        [strongSelf->_runBtn setTitle:@"▶ RUN NOW" forState:UIControlStateNormal];
    }];
}

- (void)refreshAutoLoadButtons {
    STSettings *st = [STSettings shared];
    [_autoLoadBtn setTitle:(st.autoOn ? @"AUTO LOAD: ON" : @"AUTO LOAD: OFF") forState:UIControlStateNormal];
    [_autoLoadIntervalBtn setTitle:[NSString stringWithFormat:@"كل %ld دقيقة", (long)st.autoIntervalMin] forState:UIControlStateNormal];
}

- (void)autoLoadTap {
    STSettings *st = [STSettings shared];
    st.autoOn = !st.autoOn; [st save];
    [[STAutoManager shared] refreshTimer];
    [self refreshAutoLoadButtons];
}

- (void)autoLoadIntervalTap {
    static NSArray *opts; if (!opts) opts = @[@15, @30, @60, @120];
    STSettings *st = [STSettings shared];
    NSInteger idx = [opts indexOfObject:@(st.autoIntervalMin)];
    idx = (idx == NSNotFound) ? 0 : (idx + 1) % opts.count;
    st.autoIntervalMin = [opts[idx] integerValue]; [st save];
    [[STAutoManager shared] refreshTimer];
    [self refreshAutoLoadButtons];
}
@end

#pragma mark - Main menu

static void DSKbResetSense(void);   // تصريح مسبق — التعريف الكامل في قسم الكيبورد
static NSString *DSQuickModesTitle(void);   // أوضاع الكيبورد على الكتابة السريعة
static BOOL DSQuickModesOn(void);
static void DSQuickModesToggle(void);
static void DSQuickShow(void);     // منيو الكتابة السريعة (رسالة واحدة لآخر حقل كتبت فيه)
static void DSQuickHide(void);
static void DSLiveShow(void);      // منيو السرعة الحية الصغير (مستقل عن القائمة)
static void DSLiveHide(void);
static void DSGSShow(void);        // منيو تسريع اللعبة الصغير (مستقل عن القائمة)
static void DSGSHide(void);
static void DSGSSetScale(double s);
static double DSGSGetScale(void);
static void DSGSApplyLayerSpeed(void);
static void DSLiveApplyMedia(void);
static void DSPingShow(void);      // شارة PING العائمة
static void DSPingHide(void);
static int gDSKeyOK = 0, gDSKeyAll = 0;   // عدّاد مفاتيح Agora التي قبلها المحرك (القيمة المرجعة 0) من المجموع
static void DSAgoraLowLatCycle(void);   // تقليل تأخير الصوت (Agora jitter buffer + IO buffer)
static NSString *DSAgoraLowLatTitle(void);
static BOOL DSAgoraLowLatIsOn(void);
static NSInteger DSAgoraLowLat(void);   // المستوى الحالي (0..5)
static void DSAudioGainCycle(void);   // تقوية الصوت (x1.5..x4)
static NSString *DSAudioGainTitle(void);
static BOOL DSAudioGainIsOn(void);
static void DSAudioQoSToggle(void);   // أولوية QoS (OFF / الصوت / كل اللعبة)
static NSInteger DSAudioQoSMode(void);
static NSString *DSAudioQoSTitle(void);
static BOOL DSAudioQoSIsOn(void);
static void DSAudioBufCycle(void);    // مخزن الجهاز: OFF / 5ms / 2.5ms
static NSString *DSAudioBufTitle(void);
static BOOL DSAudioBufIsOn(void);
static NSString *DSKbNumTitle(void);
static BOOL DSKbNumIsOn(void);
static void DSKbNumCycle(void);
static NSString *DSKbRevTitle(void);
static BOOL DSKbRevIsOn(void);
static void DSKbRevToggle(void);
static NSString *DSKbNamesTitle(void);
static BOOL DSKbNamesIsOn(void);
static void DSKbNamesToggle(void);
static NSInteger DSKbCatsMask(void);
static NSString *DSKbCatName(int bit);
static void DSKbCatsToggleBit(int bit);
static NSString *DSAgoraAdvTitle(void);
static void DSUltraBoot(void);
static void DSSyncBoot(void);
static double DSPingProbe(uint32_t ipBE, uint16_t portBE, double timeoutSec);
static BOOL DSPingResolveTarget(NSInteger t, uint32_t *ip, uint16_t *port, NSString **name);
static BOOL DSAgoraAdvIsOn(void);
static void DSAgoraAdvCycle(void);
static BOOL DSForceZegoOnlyIsOn(void);
static void DSForceZegoOnlyCycle(void);
static NSString *DSForceZegoOnlyTitle(void);
static void DSFlagSetBubble(BOOL on);   // زر الدول العائم (علم ← اسم/عاصمة)
static BOOL DSFlagBubbleIsOn(void);

@interface DSUltraVC : UIViewController   // القائمة الثانية: صوت Ultra + مزامنة الخادم الإداري
@end
@interface DSAudioProVC : UIViewController   // القائمة الثالثة: تقليل تأخير الصوت + معالجة الصوت
@end
static void DSAPBoot(void);
static void DSAPApplyAgora(id engine);

@interface DSMenuVC : UIViewController <UITableViewDataSource, UITableViewDelegate, UITextFieldDelegate>
@end

// مقاسات القائمة حسب الشاشة: آيباد = أزرار أكبر وأعمدة أكثر، جوال = أصغر
static CGFloat DSMenuBtnH(void) {
    CGSize z = UIScreen.mainScreen.bounds.size;
    return MIN(z.width, z.height) >= 600 ? 40 : 34;
}
static int DSMenuCols(void) {
    CGSize z = UIScreen.mainScreen.bounds.size;
    int c = (int)(z.width / 150.0);            // ~150pt لكل زر
    return c < 2 ? 2 : (c > 7 ? 7 : c);
}

@implementation DSMenuVC {
    UITableView *_tv; UITextField *_search; UISegmentedControl *_seg; UILabel *_toast, *_cursor;
    DSGradView *_header; UIView *_scan; NSMutableArray<UILabel *> *_stats; UIButton *_proxyBtn, *_liveBtn, *_gsBtn;
    NSArray<NSDictionary *> *_data; NSString *_query; NSTimer *_timer;
}

- (UIStatusBarStyle)preferredStatusBarStyle { return UIStatusBarStyleLightContent; }

- (UIButton *)neon:(NSString *)t icon:(NSString *)ic color:(UIColor *)c sel:(SEL)s {
    UIButton *b = [UIButton buttonWithType:UIButtonTypeCustom];
    [b setTitle:t forState:UIControlStateNormal]; [b setTitleColor:c forState:UIControlStateNormal];
    [b setImage:DSIcon(ic, 12) forState:UIControlStateNormal]; b.tintColor = c;
    b.titleLabel.font = [UIFont systemFontOfSize:11.5 weight:UIFontWeightHeavy]; b.imageEdgeInsets = UIEdgeInsetsMake(0, -4, 0, 4);
    b.backgroundColor = [c colorWithAlphaComponent:0.15];
    b.layer.cornerRadius = 13; b.layer.cornerCurve = kCACornerCurveContinuous;
    b.layer.borderWidth = 1.3; b.layer.borderColor = [c colorWithAlphaComponent:0.75].CGColor;
    b.layer.shadowColor = c.CGColor; b.layer.shadowOpacity = 0.4; b.layer.shadowRadius = 8; b.layer.shadowOffset = CGSizeMake(0, 2);
    [b addTarget:self action:s forControlEvents:UIControlEventTouchUpInside];
    b.titleLabel.adjustsFontSizeToFitWidth = YES; b.titleLabel.minimumScaleFactor = 0.55; b.titleLabel.numberOfLines = 1;
    b.layer.shadowRadius = 9; b.layer.shadowOpacity = 0.5;
    [b.heightAnchor constraintEqualToConstant:DSMenuBtnH()].active = YES;
    return b;
}

// عنوان قسم صغير فوق مجموعة أزرار — يعطي القائمة تنظيماً احترافياً بدل تكديس الأزرار
- (UILabel *)sectionLabel:(NSString *)t {
    UILabel *l = [UILabel new];
    l.text = [t uppercaseString];
    l.font = [UIFont systemFontOfSize:10.5 weight:UIFontWeightBold];
    l.textColor = DSHex(kGold); l.alpha = 0.85;
    return l;
}

// شبكة أزرار: كل صف أعمدة متساوية، والصف الأخير الناقص يتمدد (بدون فراغات)
- (UIStackView *)gridOf:(NSArray<UIView *> *)items {
    int cols = DSMenuCols();
    UIStackView *col = [UIStackView new]; col.axis = UILayoutConstraintAxisVertical; col.spacing = 7;
    for (NSUInteger i = 0; i < items.count; i += cols) {
        NSRange r = NSMakeRange(i, MIN((NSUInteger)cols, items.count - i));
        UIStackView *row = [[UIStackView alloc] initWithArrangedSubviews:[items subarrayWithRange:r]];
        row.distribution = UIStackViewDistributionFillEqually; row.spacing = 7;
        [col addArrangedSubview:row];
    }
    return col;
}

// بطاقة قسم: تدرّج لوني + إطار نيون متوهج + عنوان بشريط ملوّن + شبكة الأزرار
- (UIView *)card:(NSString *)title color:(UIColor *)c buttons:(NSArray<UIView *> *)btns {
    DSGradView *v = [DSGradView new];
    CAGradientLayer *gl = (CAGradientLayer *)v.layer;
    gl.colors = @[(id)[c colorWithAlphaComponent:0.22].CGColor, (id)[DSHex(kPanel) colorWithAlphaComponent:0.96].CGColor, (id)DSHex(kBG).CGColor];
    gl.startPoint = CGPointMake(0, 0); gl.endPoint = CGPointMake(1, 1);
    v.layer.cornerRadius = 16; v.layer.cornerCurve = kCACornerCurveContinuous;
    v.layer.borderWidth = 1.3; v.layer.borderColor = [c colorWithAlphaComponent:0.65].CGColor;
    v.layer.shadowColor = c.CGColor; v.layer.shadowOpacity = 0.35; v.layer.shadowRadius = 10; v.layer.shadowOffset = CGSizeMake(0, 2);

    UILabel *t = [UILabel new];
    NSMutableAttributedString *as = [[NSMutableAttributedString alloc] initWithString:@"▍" attributes:@{
        NSForegroundColorAttributeName: c, NSFontAttributeName: [UIFont systemFontOfSize:15 weight:UIFontWeightHeavy] }];
    [as appendAttributedString:[[NSAttributedString alloc] initWithString:[@" " stringByAppendingString:title] attributes:@{
        NSForegroundColorAttributeName: DSHex(kText), NSFontAttributeName: [UIFont systemFontOfSize:12.5 weight:UIFontWeightHeavy], NSKernAttributeName: @(0.6) }]];
    t.attributedText = as; DSGlow(t.layer, c, 5);

    UIStackView *st = [[UIStackView alloc] initWithArrangedSubviews:@[t, [self gridOf:btns]]];
    st.axis = UILayoutConstraintAxisVertical; st.spacing = 8; st.translatesAutoresizingMaskIntoConstraints = NO;
    [v addSubview:st];
    [NSLayoutConstraint activateConstraints:@[
        [st.topAnchor constraintEqualToAnchor:v.topAnchor constant:9], [st.bottomAnchor constraintEqualToAnchor:v.bottomAnchor constant:-10],
        [st.leadingAnchor constraintEqualToAnchor:v.leadingAnchor constant:10], [st.trailingAnchor constraintEqualToAnchor:v.trailingAnchor constant:-10]]];
    return v;
}

- (UIView *)statCard:(NSString *)cap color:(UIColor *)c {
    UIView *v = [UIView new]; v.backgroundColor = DSHex(kPanel); v.layer.cornerRadius = 12; v.layer.cornerCurve = kCACornerCurveContinuous;
    v.layer.borderWidth = 1; v.layer.borderColor = [c colorWithAlphaComponent:0.45].CGColor;
    v.layer.shadowColor = c.CGColor; v.layer.shadowOpacity = 0.25; v.layer.shadowRadius = 8; v.layer.shadowOffset = CGSizeZero;
    UILabel *n = [UILabel new]; n.text = @"0"; n.font = DSMono(20, UIFontWeightBold); n.textColor = c; n.textAlignment = NSTextAlignmentCenter;
    DSGlow(n.layer, c, 6);
    UILabel *k = [UILabel new]; k.text = cap; k.font = DSMono(9, UIFontWeightSemibold); k.textColor = DSHex(kDim); k.textAlignment = NSTextAlignmentCenter;
    UIStackView *st = [[UIStackView alloc] initWithArrangedSubviews:@[n, k]];
    st.axis = UILayoutConstraintAxisVertical; st.spacing = 2; st.translatesAutoresizingMaskIntoConstraints = NO;
    [v addSubview:st];
    [NSLayoutConstraint activateConstraints:@[
        [st.topAnchor constraintEqualToAnchor:v.topAnchor constant:10], [st.bottomAnchor constraintEqualToAnchor:v.bottomAnchor constant:-8],
        [st.leadingAnchor constraintEqualToAnchor:v.leadingAnchor constant:4], [st.trailingAnchor constraintEqualToAnchor:v.trailingAnchor constant:-4]]];
    [_stats addObject:n];
    return v;
}

- (void)viewDidLoad {
    [super viewDidLoad];
    self.overrideUserInterfaceStyle = UIUserInterfaceStyleDark;
    self.view.backgroundColor = DSHex(kBG);
    _stats = [NSMutableArray array];

    // ----- header -----
    _header = [DSGradView new];
    CAGradientLayer *gl = (CAGradientLayer *)_header.layer;
    gl.colors = @[(id)DSHex(0x2E1A5C).CGColor, (id)DSHex(0x120A26).CGColor, (id)DSHex(kBG).CGColor];
    gl.startPoint = CGPointMake(0, 0); gl.endPoint = CGPointMake(1, 1);
    _header.layer.cornerRadius = 18; _header.layer.cornerCurve = kCACornerCurveContinuous; _header.layer.borderWidth = 1.5;
    _header.layer.borderColor = [DSHex(kGold) colorWithAlphaComponent:0.9].CGColor; _header.clipsToBounds = YES;

    UILabel *logo = [UILabel new];
    NSMutableAttributedString *logoStr = [[NSMutableAttributedString alloc] initWithString:@"♛  AFLATOON SUITE"
        attributes:@{ NSFontAttributeName: DSMono(20, UIFontWeightHeavy), NSForegroundColorAttributeName: DSHex(kGold), NSKernAttributeName: @(2.2) }];
    logo.attributedText = logoStr;
    DSGlow(logo.layer, DSHex(kGold), 10); logo.adjustsFontSizeToFitWidth = YES; logo.minimumScaleFactor = 0.6;
    UIButton *close = [UIButton buttonWithType:UIButtonTypeSystem];
    [close setImage:DSIcon(@"xmark.circle.fill", 24) forState:UIControlStateNormal]; close.tintColor = DSHex(kRed);
    [close addTarget:self action:@selector(closeTap) forControlEvents:UIControlEventTouchUpInside];
    [close setContentHuggingPriority:UILayoutPriorityRequired forAxis:UILayoutConstraintAxisHorizontal];
    UIStackView *row1 = [[UIStackView alloc] initWithArrangedSubviews:@[logo, close]]; row1.alignment = UIStackViewAlignmentCenter;

    UILabel *prompt = [UILabel new]; prompt.text = @"$ plato --exclusive --sniff --test --auto"; prompt.font = DSMono(11, UIFontWeightMedium); prompt.textColor = DSHex(kCyan);
    _cursor = [UILabel new]; _cursor.text = @"█"; _cursor.font = DSMono(11, UIFontWeightBold); _cursor.textColor = DSHex(kGold);
    [_cursor setContentHuggingPriority:UILayoutPriorityRequired forAxis:UILayoutConstraintAxisHorizontal];
    UIStackView *row2 = [[UIStackView alloc] initWithArrangedSubviews:@[prompt, _cursor]]; row2.spacing = 3;

    UIView *creditBadge = [UIView new];
    creditBadge.backgroundColor = [DSHex(kGold) colorWithAlphaComponent:0.18];
    creditBadge.layer.cornerRadius = 9; creditBadge.layer.cornerCurve = kCACornerCurveContinuous;
    creditBadge.layer.borderWidth = 1.2; creditBadge.layer.borderColor = [DSHex(kGold) colorWithAlphaComponent:0.9].CGColor; DSGlow(creditBadge.layer, DSHex(kGold), 7); creditBadge.layer.shadowOpacity = 0.35;
    UILabel *creditIcon = [UILabel new]; creditIcon.text = @"♛"; creditIcon.font = [UIFont systemFontOfSize:11]; creditIcon.textColor = DSHex(kGold);
    UILabel *credit = [UILabel new]; credit.text = @"© أفلاطون  •  Aflatoon — جميع الحقوق محفوظة";
    credit.font = [UIFont systemFontOfSize:11.5 weight:UIFontWeightHeavy]; credit.textColor = DSHex(kGold);
    credit.adjustsFontSizeToFitWidth = YES; credit.minimumScaleFactor = 0.65;
    UIStackView *creditRow = [[UIStackView alloc] initWithArrangedSubviews:@[creditIcon, credit]];
    creditRow.spacing = 5; creditRow.alignment = UIStackViewAlignmentCenter; creditRow.translatesAutoresizingMaskIntoConstraints = NO;
    [creditBadge addSubview:creditRow];
    [NSLayoutConstraint activateConstraints:@[
        [creditRow.topAnchor constraintEqualToAnchor:creditBadge.topAnchor constant:4], [creditRow.bottomAnchor constraintEqualToAnchor:creditBadge.bottomAnchor constant:-4],
        [creditRow.leadingAnchor constraintEqualToAnchor:creditBadge.leadingAnchor constant:9], [creditRow.trailingAnchor constraintEqualToAnchor:creditBadge.trailingAnchor constant:-9]]];
    UIStackView *creditWrap = [[UIStackView alloc] initWithArrangedSubviews:@[creditBadge, [UIView new]]];   // يدفع الشارة لليسار بدل تمديدها كامل العرض

    UIStackView *hs = [[UIStackView alloc] initWithArrangedSubviews:@[row1, row2, creditWrap]];
    hs.axis = UILayoutConstraintAxisVertical; hs.spacing = 5; hs.translatesAutoresizingMaskIntoConstraints = NO;
    [_header addSubview:hs];
    [NSLayoutConstraint activateConstraints:@[
        [hs.topAnchor constraintEqualToAnchor:_header.topAnchor constant:12], [hs.bottomAnchor constraintEqualToAnchor:_header.bottomAnchor constant:-12],
        [hs.leadingAnchor constraintEqualToAnchor:_header.leadingAnchor constant:14], [hs.trailingAnchor constraintEqualToAnchor:_header.trailingAnchor constant:-10]]];
    _scan = [UIView new]; _scan.backgroundColor = [DSHex(kGold) colorWithAlphaComponent:0.55]; _scan.userInteractionEnabled = NO;
    [_header addSubview:_scan];

    // ----- stats -----
    UIStackView *stats = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self statCard:@"TOTAL" color:DSHex(kGreen)], [self statCard:@"DOMAINS" color:DSHex(kCyan)],
        [self statCard:@"IPS" color:DSHex(kAmber)], [self statCard:@"BLOCKED" color:DSHex(kRed)]]];
    stats.distribution = UIStackViewDistributionFillEqually; stats.spacing = 8;

    // ----- search -----
    _search = [UITextField new]; _search.delegate = self; _search.font = DSMono(14, UIFontWeightRegular); _search.textColor = DSHex(kText);
    _search.attributedPlaceholder = [[NSAttributedString alloc] initWithString:@"grep  domain | ip" attributes:@{ NSForegroundColorAttributeName: DSHex(kDim), NSFontAttributeName: DSMono(14, UIFontWeightRegular) }];
    _search.backgroundColor = DSHex(kPanel); _search.layer.cornerRadius = 12; _search.layer.borderWidth = 1; _search.layer.borderColor = [DSHex(kGold) colorWithAlphaComponent:0.5].CGColor;
    _search.autocapitalizationType = UITextAutocapitalizationTypeNone; _search.autocorrectionType = UITextAutocorrectionTypeNo;
    _search.clearButtonMode = UITextFieldViewModeWhileEditing; _search.returnKeyType = UIReturnKeySearch; _search.keyboardAppearance = UIKeyboardAppearanceDark;
    UIImageView *mag = [[UIImageView alloc] initWithImage:DSIcon(@"magnifyingglass", 14)]; mag.tintColor = DSHex(kGold); mag.contentMode = UIViewContentModeCenter;
    mag.frame = CGRectMake(0, 0, 36, 40); _search.leftView = mag; _search.leftViewMode = UITextFieldViewModeAlways;
    [_search addTarget:self action:@selector(queryChanged:) forControlEvents:UIControlEventEditingChanged];
    [_search.heightAnchor constraintEqualToConstant:40].active = YES;

    // ----- filter -----
    _seg = [[UISegmentedControl alloc] initWithItems:@[@"ALL", @"DOMAINS", @"IP", @"BLOCKED"]];
    _seg.selectedSegmentIndex = 0; _seg.backgroundColor = DSHex(kPanel); _seg.selectedSegmentTintColor = DSHex(kGold);
    [_seg setTitleTextAttributes:@{ NSForegroundColorAttributeName: DSHex(kDim), NSFontAttributeName: DSMono(11, UIFontWeightBold) } forState:UIControlStateNormal];
    [_seg setTitleTextAttributes:@{ NSForegroundColorAttributeName: DSHex(kBG), NSFontAttributeName: DSMono(11, UIFontWeightHeavy) } forState:UIControlStateSelected];
    [_seg addTarget:self action:@selector(reload) forControlEvents:UIControlEventValueChanged];

    // ----- table -----
    _tv = [[UITableView alloc] initWithFrame:CGRectZero style:UITableViewStylePlain];
    _tv.dataSource = self; _tv.delegate = self; _tv.backgroundColor = UIColor.clearColor; _tv.separatorStyle = UITableViewCellSeparatorStyleNone;
    _tv.rowHeight = UITableViewAutomaticDimension; _tv.estimatedRowHeight = 84; _tv.keyboardDismissMode = UIScrollViewKeyboardDismissModeOnDrag;
    [_tv registerClass:DSCell.class forCellReuseIdentifier:@"c"];
    [_tv setContentHuggingPriority:1 forAxis:UILayoutConstraintAxisVertical];
    [_tv setContentCompressionResistancePriority:1 forAxis:UILayoutConstraintAxisVertical];

    // ----- actions -----
    UIStackView *bar1 = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:@"SAVE" icon:@"square.and.arrow.down" color:DSHex(kGreen) sel:@selector(saveTap)],
        [self neon:@"SHARE" icon:@"square.and.arrow.up" color:DSHex(kCyan) sel:@selector(shareTap:)],
        [self neon:@"COPY" icon:@"doc.on.doc" color:DSHex(kPurple) sel:@selector(copyTap)],
        [self neon:@"CLEAR" icon:@"trash" color:DSHex(kRed) sel:@selector(clearTap)]]];
    bar1.distribution = UIStackViewDistributionFillEqually; bar1.spacing = 8;
    UIStackView *bar2 = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:@"NEXTDNS KEY" icon:@"key.fill" color:DSHex(kAmber) sel:@selector(apiTap)],
        [self neon:@"RULES" icon:@"arrow.triangle.2.circlepath" color:DSHex(kGreen) sel:@selector(rulesTap)],
        [self neon:([DSSettings shared].autoDNS ? @"DNS 8.8.8.8" : @"DNS OFF") icon:@"globe"
             color:([DSSettings shared].autoDNS ? DSHex(kCyan) : DSHex(kDim)) sel:@selector(dnsTap:)]]];
    bar2.distribution = UIStackViewDistributionFillEqually; bar2.spacing = 8;

    UIStackView *bar3 = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:([DSSettings shared].forceAll ? @"ALL → 8.8.8.8 : ON" : @"ALL → 8.8.8.8 : OFF") icon:@"bolt.fill"
             color:([DSSettings shared].forceAll ? DSHex(kRed) : DSHex(kDim)) sel:@selector(forceTap:)],
        [self neon:([DSSettings shared].chatMode ? @"CHAT → 8.8.8.8" : @"CHAT OFF") icon:@"bubble.left.and.bubble.right"
             color:([DSSettings shared].chatMode ? DSHex(kGreen) : DSHex(kDim)) sel:@selector(chatTap:)]]];

    _proxyBtn = [self neon:[self proxyTitle] icon:@"network" color:([DSProxy shared].enabled ? DSHex(kGreen) : DSHex(kDim)) sel:@selector(proxyTap:)];
    _proxyBtn.titleLabel.adjustsFontSizeToFitWidth = YES; _proxyBtn.titleLabel.minimumScaleFactor = 0.7;
    UIStackView *barP = [[UIStackView alloc] initWithArrangedSubviews:@[
        _proxyBtn,
        [self neon:@"PROXY LINK" icon:@"link" color:DSHex(kAmber) sel:@selector(proxyLinkTap)],
        [self neon:@"TEST" icon:@"checkmark.seal" color:DSHex(kCyan) sel:@selector(proxyTestTap)]]];
    barP.distribution = UIStackViewDistributionFillEqually; barP.spacing = 6;

    UIStackView *bar4 = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:([DSSettings shared].joinSoundOn ? @"JOIN SOUND: ON" : @"JOIN SOUND: OFF") icon:@"speaker.wave.2.fill"
             color:([DSSettings shared].joinSoundOn ? DSHex(kCyan) : DSHex(kDim)) sel:@selector(joinSoundTap:)],
        [self neon:[NSString stringWithFormat:@"SPEED x%d", (int)[DSSettings shared].joinSoundRate] icon:@"gauge.with.dots.needle.67percent"
             color:DSHex(kAmber) sel:@selector(joinSpeedTap:)]]];
    bar4.distribution = UIStackViewDistributionFillEqually; bar4.spacing = 6;

    UIStackView *bar5 = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:([DSSettings shared].voiceSpeedOn ? @"VOICE SPEED: ON" : @"VOICE SPEED: OFF") icon:@"waveform"
             color:([DSSettings shared].voiceSpeedOn ? DSHex(kPurple) : DSHex(kDim)) sel:@selector(voiceSpeedTap:)],
        [self neon:[NSString stringWithFormat:@"MAX x%d", (int)[DSSettings shared].voiceSpeedMax] icon:@"gauge.with.dots.needle.67percent"
             color:DSHex(kAmber) sel:@selector(voiceSpeedMaxTap:)]]];
    bar5.distribution = UIStackViewDistributionFillEqually; bar5.spacing = 6;

    UIStackView *barK = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:([DSSettings shared].kbRepeatNums ? @"تكرار الأرقام: ON" : @"تكرار الأرقام: OFF") icon:@"repeat"
             color:([DSSettings shared].kbRepeatNums ? DSHex(kAmber) : DSHex(kDim)) sel:@selector(kbRepeatTap:)],
        [self neon:([DSSettings shared].kbSplitLetters ? @"تفكيك الحروف: ON" : @"تفكيك الحروف: OFF") icon:@"textformat"
             color:([DSSettings shared].kbSplitLetters ? DSHex(kPurple) : DSHex(kDim)) sel:@selector(kbSplitTap:)]]];
    barK.distribution = UIStackViewDistributionFillEqually; barK.spacing = 6;
    for (UIButton *kb in (NSArray<UIButton *> *)barK.arrangedSubviews) { kb.titleLabel.adjustsFontSizeToFitWidth = YES; kb.titleLabel.minimumScaleFactor = 0.7; }

    UIStackView *barK2 = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:([DSSettings shared].kbSense ? @"حساسية الكيبورد: ON" : @"حساسية الكيبورد: OFF") icon:@"hand.tap"
             color:([DSSettings shared].kbSense ? DSHex(kGreen) : DSHex(kDim)) sel:@selector(kbSenseTap:)],
        [self neon:[self kbSenseModeTitle] icon:@"slider.horizontal.3"
             color:DSHex(kCyan) sel:@selector(kbSenseModeTap:)]]];
    barK2.distribution = UIStackViewDistributionFillEqually; barK2.spacing = 6;
    for (UIButton *kb in (NSArray<UIButton *> *)barK2.arrangedSubviews) { kb.titleLabel.adjustsFontSizeToFitWidth = YES; kb.titleLabel.minimumScaleFactor = 0.7; }

    UIStackView *barK3 = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:[NSString stringWithFormat:@"أقل عدد أحرف: %ld", (long)[DSSettings shared].kbMinChars] icon:@"number"
             color:DSHex(kAmber) sel:@selector(kbMinCharsTap:)],
        [self neon:([DSSettings shared].kbHaptic ? @"اهتزاز عند الارسال: ON" : @"اهتزاز عند الارسال: OFF") icon:@"waveform.path"
             color:([DSSettings shared].kbHaptic ? DSHex(kPurple) : DSHex(kDim)) sel:@selector(kbHapticTap:)]]];
    barK3.distribution = UIStackViewDistributionFillEqually; barK3.spacing = 6;
    for (UIButton *kb in (NSArray<UIButton *> *)barK3.arrangedSubviews) { kb.titleLabel.adjustsFontSizeToFitWidth = YES; kb.titleLabel.minimumScaleFactor = 0.7; }

    UIStackView *barK5 = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:DSKbNumTitle() icon:@"number"
             color:(DSKbNumIsOn() ? DSHex(kAmber) : DSHex(kDim)) sel:@selector(kbNumTap:)],
        [self neon:DSKbRevTitle() icon:@"arrow.left.arrow.right"
             color:(DSKbRevIsOn() ? DSHex(kPurple) : DSHex(kDim)) sel:@selector(kbRevTap:)]]];
    barK5.distribution = UIStackViewDistributionFillEqually; barK5.spacing = 6;
    for (UIButton *kb in (NSArray<UIButton *> *)barK5.arrangedSubviews) { kb.titleLabel.adjustsFontSizeToFitWidth = YES; kb.titleLabel.minimumScaleFactor = 0.7; }

    UIStackView *barK6 = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:DSKbNamesTitle() icon:@"character.book.closed.fill"
             color:(DSKbNamesIsOn() ? DSHex(kGreen) : DSHex(kDim)) sel:@selector(kbNamesTap:)],
        [self neon:@"فئات الأسماء" icon:@"checklist"
             color:DSHex(kCyan) sel:@selector(kbCatsTap:)]]];
    barK6.distribution = UIStackViewDistributionFillEqually; barK6.spacing = 6;
    for (UIButton *kb in (NSArray<UIButton *> *)barK6.arrangedSubviews) { kb.titleLabel.adjustsFontSizeToFitWidth = YES; kb.titleLabel.minimumScaleFactor = 0.7; }

    UIStackView *barK4 = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:DSDigitSendTitle() icon:@"number.circle.fill"
             color:(DSDigitSendIsOn() ? DSHex(kGreen) : DSHex(kDim)) sel:@selector(digitSendTap:)]]];
    for (UIButton *kb in (NSArray<UIButton *> *)barK4.arrangedSubviews) { kb.titleLabel.adjustsFontSizeToFitWidth = YES; kb.titleLabel.minimumScaleFactor = 0.6; }
    barK4.distribution = UIStackViewDistributionFillEqually; barK4.spacing = 6;

    UIStackView *bar5b = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:DSQuickModesTitle() icon:@"text.badge.checkmark"
             color:(DSQuickModesOn() ? DSHex(kGreen) : DSHex(kDim)) sel:@selector(quickModesTap:)]]];
    bar5b.distribution = UIStackViewDistributionFillEqually; bar5b.spacing = 6;

    UIStackView *bar5c = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:([DSSettings shared].quickSendOn ? @"الكتابة السريعة: ON" : @"الكتابة السريعة: OFF") icon:@"text.bubble.fill"
             color:([DSSettings shared].quickSendOn ? DSHex(kGreen) : DSHex(kDim)) sel:@selector(quickSendTap:)]]];
    bar5c.distribution = UIStackViewDistributionFillEqually; bar5c.spacing = 6;

    UIStackView *barPing = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:[self pingTitle] icon:@"wifi"
             color:([DSSettings shared].pingOn ? DSHex(kGreen) : DSHex(kDim)) sel:@selector(pingTap:)]]];
    barPing.distribution = UIStackViewDistributionFillEqually; barPing.spacing = 6;

    UIStackView *barNtg = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:[self ntgTitle] icon:@"phone.connection"
             color:(DS_NTG_LINKED ? DSHex(kGreen) : DSHex(kDim)) sel:@selector(ntgTap:)]]];
    barNtg.distribution = UIStackViewDistributionFillEqually; barNtg.spacing = 6;

    UIStackView *bar5f = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:DSAgoraLowLatTitle() icon:@"bolt.fill"
             color:(DSAgoraLowLatIsOn() ? DSHex(kGreen) : DSHex(kDim)) sel:@selector(lowLatTap:)]]];
    bar5f.distribution = UIStackViewDistributionFillEqually; bar5f.spacing = 6;

    UIStackView *bar5q = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:DSAudioGainTitle() icon:@"speaker.wave.3.fill"
             color:(DSAudioGainIsOn() ? DSHex(kGreen) : DSHex(kDim)) sel:@selector(audioGainTap:)]]];
    bar5q.distribution = UIStackViewDistributionFillEqually; bar5q.spacing = 6;

    UIStackView *bar5r = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:DSAudioQoSTitle() icon:@"antenna.radiowaves.left.and.right"
             color:(DSAudioQoSIsOn() ? DSHex(kGreen) : DSHex(kDim)) sel:@selector(audioQoSTap:)]]];
    bar5r.distribution = UIStackViewDistributionFillEqually; bar5r.spacing = 6;

    UIStackView *bar5s = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:DSAudioBufTitle() icon:@"waveform"
             color:(DSAudioBufIsOn() ? DSHex(kGreen) : DSHex(kDim)) sel:@selector(audioBufTap:)]]];
    bar5s.distribution = UIStackViewDistributionFillEqually; bar5s.spacing = 6;

    UIStackView *bar5u = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:@"ULTRA ⚡  القائمة الثانية: صوت + مزامنة الخادم" icon:@"bolt.horizontal.circle.fill"
             color:DSHex(kPurple) sel:@selector(ultraTap:)]]];
    bar5u.distribution = UIStackViewDistributionFillEqually; bar5u.spacing = 6;

    UIStackView *bar5v = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:@"AUDIO PRO 🎚  القائمة الثالثة: تأخير أقل + معالجة صوت" icon:@"slider.vertical.3"
             color:DSHex(kCyan) sel:@selector(audioProTap:)]]];
    bar5v.distribution = UIStackViewDistributionFillEqually; bar5v.spacing = 6;

    UIStackView *bar5t = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:DSAgoraAdvTitle() icon:@"slider.horizontal.below.rectangle"
             color:(DSAgoraAdvIsOn() ? DSHex(kGreen) : DSHex(kDim)) sel:@selector(agoraAdvTap:)]]];
    bar5t.distribution = UIStackViewDistributionFillEqually; bar5t.spacing = 6;

    UIStackView *bar5g = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:DSForceZegoOnlyTitle() icon:@"xmark.icloud.fill"
             color:(DSForceZegoOnlyIsOn() ? DSHex(kRed) : DSHex(kDim)) sel:@selector(forceZegoTap:)]]];
    bar5g.distribution = UIStackViewDistributionFillEqually; bar5g.spacing = 6;

    UIStackView *bar5e = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:(DSFlagBubbleIsOn() ? @"الدول (علم ← اسم/عاصمة): ON" : @"الدول (علم ← اسم/عاصمة): OFF") icon:@"flag.fill"
             color:(DSFlagBubbleIsOn() ? DSHex(kGreen) : DSHex(kDim)) sel:@selector(flagTap:)]]];
    bar5e.distribution = UIStackViewDistributionFillEqually; bar5e.spacing = 6;

    _liveBtn = [self neon:[self liveTitle] icon:@"gauge.with.dots.needle.67percent"
             color:([DSSettings shared].liveSpeedOn ? DSHex(kPurple) : DSHex(kDim)) sel:@selector(liveSpeedTap:)];
    _liveBtn.titleLabel.adjustsFontSizeToFitWidth = YES; _liveBtn.titleLabel.minimumScaleFactor = 0.7;
    UIStackView *bar5d = [[UIStackView alloc] initWithArrangedSubviews:@[_liveBtn]];
    bar5d.distribution = UIStackViewDistributionFillEqually; bar5d.spacing = 6;
    [[NSNotificationCenter defaultCenter] addObserver:self selector:@selector(liveSync) name:DSLiveSettingNote object:nil];

    _gsBtn = [self neon:[self gsTitle] icon:@"hare.fill"
             color:([NSUserDefaults.standardUserDefaults boolForKey:@"DSGameSpeedOn"] ? DSHex(kAmber) : DSHex(kDim)) sel:@selector(gsTap:)];
    _gsBtn.titleLabel.adjustsFontSizeToFitWidth = YES; _gsBtn.titleLabel.minimumScaleFactor = 0.7;
    UIStackView *bar5h = [[UIStackView alloc] initWithArrangedSubviews:@[_gsBtn]];
    bar5h.distribution = UIStackViewDistributionFillEqually; bar5h.spacing = 6;
    [[NSNotificationCenter defaultCenter] addObserver:self selector:@selector(gsSync) name:DSGSSettingNote object:nil];

    UIStackView *bar6 = [[UIStackView alloc] initWithArrangedSubviews:@[
        [self neon:@"⚡ SERVER TEST" icon:@"bolt.fill" color:DSHex(kGreen) sel:@selector(serverTestTap)]]];
    bar6.distribution = UIStackViewDistributionFillEqually; bar6.spacing = 6;
    bar3.distribution = UIStackViewDistributionFillEqually; bar3.spacing = 6;

    UILabel *foot = [UILabel new]; foot.text = @"♛  © أفلاطون // Aflatoon — جميع الحقوق محفوظة  ♛"; foot.textAlignment = NSTextAlignmentCenter;
    foot.font = [UIFont systemFontOfSize:11.5 weight:UIFontWeightHeavy]; foot.textColor = DSHex(kGold);
    DSGlow(foot.layer, DSHex(kGold), 6); foot.layer.shadowOpacity = 0.55; foot.adjustsFontSizeToFitWidth = YES; foot.minimumScaleFactor = 0.7;

    // ----- كل الأزرار ظاهرة بدون سكرول: بطاقات أقسام بشبكة أعمدة -----
    NSArray *(^flat)(NSArray<UIStackView *> *) = ^NSArray *(NSArray<UIStackView *> *bars) {
        NSMutableArray *a = [NSMutableArray array];
        for (UIStackView *bar in bars) [a addObjectsFromArray:bar.arrangedSubviews];   // نسخة، ثم تنتقل الأزرار للشبكة
        return a;
    };
    UIView *cData = [self card:@"ادارة البيانات" color:DSHex(kGreen) buttons:flat(@[bar1])];
    UIView *cNet  = [self card:@"الشبكة · DNS · الاختبار" color:DSHex(kCyan) buttons:flat(@[bar2, bar3, barP, barPing, bar6])];
    UIView *cChat = [self card:@"الدردشة والصوت" color:DSHex(kPurple) buttons:flat(@[bar4, bar5, bar5d, bar5h, bar5b, bar5c, bar5f, bar5q, bar5s, bar5r, bar5t, bar5u, bar5v, bar5g, barNtg, bar5e])];
    UIView *cKb   = [self card:@"الكيبورد" color:DSHex(kAmber) buttons:flat(@[barK, barK2, barK3, barK4, barK5, barK6])];

    UIStackView *main = [[UIStackView alloc] initWithArrangedSubviews:@[_header, stats, _search, _seg, _tv, cData, cNet, cChat, cKb, foot]];
    main.axis = UILayoutConstraintAxisVertical; main.spacing = 8; main.translatesAutoresizingMaskIntoConstraints = NO;
    UILayoutGuide *g = self.view.safeAreaLayoutGuide;
    CGSize scr = UIScreen.mainScreen.bounds.size;
    BOOL fitsNoScroll = MIN(scr.width, scr.height) >= 600 && scr.height >= 900;   // آيباد طولي: كل شي يظهر بلا سكرول
    if (fitsNoScroll) {
        [self.view addSubview:main];
        NSLayoutConstraint *minTv = [_tv.heightAnchor constraintGreaterThanOrEqualToConstant:120]; minTv.priority = UILayoutPriorityDefaultHigh;
        [NSLayoutConstraint activateConstraints:@[
            minTv,
            [main.topAnchor constraintEqualToAnchor:g.topAnchor constant:8], [main.bottomAnchor constraintEqualToAnchor:g.bottomAnchor constant:-6],
            [main.leadingAnchor constraintEqualToAnchor:g.leadingAnchor constant:14], [main.trailingAnchor constraintEqualToAnchor:g.trailingAnchor constant:-14]]];
    } else {   // شاشة صغيرة/أفقية: نفس التصميم داخل سكرول حتى لا ينكسر شي
        UIScrollView *sv = [UIScrollView new]; sv.translatesAutoresizingMaskIntoConstraints = NO;
        sv.alwaysBounceVertical = YES; sv.showsVerticalScrollIndicator = NO; sv.keyboardDismissMode = UIScrollViewKeyboardDismissModeOnDrag;
        [self.view addSubview:sv]; [sv addSubview:main];
        [NSLayoutConstraint activateConstraints:@[
            [sv.topAnchor constraintEqualToAnchor:g.topAnchor], [sv.bottomAnchor constraintEqualToAnchor:g.bottomAnchor],
            [sv.leadingAnchor constraintEqualToAnchor:g.leadingAnchor], [sv.trailingAnchor constraintEqualToAnchor:g.trailingAnchor],
            [main.topAnchor constraintEqualToAnchor:sv.contentLayoutGuide.topAnchor constant:8],
            [main.bottomAnchor constraintEqualToAnchor:sv.contentLayoutGuide.bottomAnchor constant:-10],
            [main.leadingAnchor constraintEqualToAnchor:sv.frameLayoutGuide.leadingAnchor constant:14],
            [main.trailingAnchor constraintEqualToAnchor:sv.frameLayoutGuide.trailingAnchor constant:-14],
            [_tv.heightAnchor constraintEqualToConstant:220]]];
    }

    _toast = [UILabel new]; _toast.backgroundColor = DSHex(kPanel); _toast.textColor = DSHex(kGreen); _toast.textAlignment = NSTextAlignmentCenter;
    _toast.font = DSMono(12, UIFontWeightBold); _toast.layer.cornerRadius = 10; _toast.layer.borderWidth = 1; _toast.layer.borderColor = DSHex(kGreen).CGColor;
    _toast.clipsToBounds = YES; _toast.alpha = 0; _toast.adjustsFontSizeToFitWidth = YES; _toast.minimumScaleFactor = 0.7;
    _toast.translatesAutoresizingMaskIntoConstraints = NO; [self.view addSubview:_toast];
    [NSLayoutConstraint activateConstraints:@[
        [_toast.centerXAnchor constraintEqualToAnchor:self.view.centerXAnchor], [_toast.bottomAnchor constraintEqualToAnchor:g.bottomAnchor constant:-120],
        [_toast.widthAnchor constraintGreaterThanOrEqualToConstant:180], [_toast.widthAnchor constraintLessThanOrEqualToAnchor:self.view.widthAnchor constant:-40],
        [_toast.heightAnchor constraintEqualToConstant:38]]];
    [self reload];
}

- (void)viewWillAppear:(BOOL)animated {
    [super viewWillAppear:animated];
    _timer = [NSTimer scheduledTimerWithTimeInterval:1.5 target:self selector:@selector(reload) userInfo:nil repeats:YES];
    CABasicAnimation *b = [CABasicAnimation animationWithKeyPath:@"opacity"];
    b.fromValue = @1; b.toValue = @0; b.duration = 0.55; b.autoreverses = YES; b.repeatCount = HUGE_VALF;
    [_cursor.layer addAnimation:b forKey:@"blink"];
}
- (void)viewDidAppear:(BOOL)animated {
    [super viewDidAppear:animated];
    [self.view layoutIfNeeded];
    CGFloat w = _header.bounds.size.width, h = _header.bounds.size.height;
    _scan.frame = CGRectMake(0, 0, w, 1.5);
    [UIView animateWithDuration:2.6 delay:0 options:UIViewAnimationOptionRepeat | UIViewAnimationOptionCurveLinear animations:^{
        self->_scan.frame = CGRectMake(0, h - 1.5, w, 1.5);
    } completion:nil];
}
- (void)viewDidDisappear:(BOOL)animated { [super viewDidDisappear:animated]; [_timer invalidate]; _timer = nil; }

- (void)reload {
    if (_proxyBtn) [self styleProxyBtn];
    NSInteger m = _seg.selectedSegmentIndex;
    NSString *q = _query.lowercaseString;
    NSArray *all = [[DSStore shared] snapshot];
    NSMutableArray *out = [NSMutableArray array];
    NSUInteger nd = 0, ni = 0, nb = 0;
    for (NSDictionary *e in all) {
        BOOL dom = [e[@"type"] isEqualToString:@"domain"], blk = [e[@"status"] isEqualToString:@"BLOCKED"];
        if (dom) nd++; else ni++;
        if (blk) nb++;
        if (m == 1 && !dom) continue;
        if (m == 2 && dom) continue;
        if (m == 3 && !blk) continue;
        if (q.length) {
            NSString *hay = [[NSString stringWithFormat:@"%@ %@", e[@"value"], [e[@"related"] componentsJoinedByString:@" "]] lowercaseString];
            if (![hay containsString:q]) continue;
        }
        [out addObject:e];
    }
    _data = out;
    NSArray *nums = @[@(all.count), @(nd), @(ni), @(nb)];
    for (NSUInteger i = 0; i < _stats.count; i++) _stats[i].text = [nums[i] stringValue];
    [_tv reloadData];
}

- (void)toast:(NSString *)t {
    _toast.text = t;
    [_toast.layer removeAllAnimations];
    [UIView animateWithDuration:0.2 animations:^{ self->_toast.alpha = 1; } completion:^(BOOL f) {
        [UIView animateWithDuration:0.3 delay:1.8 options:0 animations:^{ self->_toast.alpha = 0; } completion:nil];
    }];
}

- (void)closeTap { [self dismissViewControllerAnimated:YES completion:nil]; }
- (void)queryChanged:(UITextField *)t { _query = t.text; [self reload]; }
- (BOOL)textFieldShouldReturn:(UITextField *)t { [t resignFirstResponder]; return YES; }

- (void)dnsTap:(UIButton *)b {
    DSSettings *st = [DSSettings shared];
    st.autoDNS = !st.autoDNS; [st save];
    UIColor *c = st.autoDNS ? DSHex(kCyan) : DSHex(kDim);
    [b setTitle:(st.autoDNS ? @"DNS 8.8.8.8" : @"DNS OFF") forState:UIControlStateNormal];
    [b setTitleColor:c forState:UIControlStateNormal]; b.tintColor = c;
    b.backgroundColor = [c colorWithAlphaComponent:0.12];
    b.titleLabel.adjustsFontSizeToFitWidth = YES; b.titleLabel.minimumScaleFactor = 0.7;
    [self toast:(st.autoDNS ? @"DNS تلقائي → 8.8.8.8 ✅" : @"DNS التلقائي متوقف")];
}

- (void)forceTap:(UIButton *)b {   // يعمل لحظياً: الأعلام تُقرأ عند كل اتصال جديد
    DSSettings *st = [DSSettings shared];
    st.forceAll = !st.forceAll; [st save];
    UIColor *c = st.forceAll ? DSHex(kRed) : DSHex(kDim);
    [b setTitle:(st.forceAll ? @"ALL → 8.8.8.8 : ON" : @"ALL → 8.8.8.8 : OFF") forState:UIControlStateNormal];
    [b setTitleColor:c forState:UIControlStateNormal]; b.tintColor = c;
    b.backgroundColor = [c colorWithAlphaComponent:0.12];
    b.titleLabel.adjustsFontSizeToFitWidth = YES; b.titleLabel.minimumScaleFactor = 0.7;
    [self toast:(st.forceAll ? @"كل النطاقات والـ IPs → 8.8.8.8 ⚡" : @"رجع الوضع الطبيعي")];
}

- (NSString *)proxyTitle {
    DSProxy *p = [DSProxy shared];
    if (!p.enabled) return @"PROXY: OFF";
    return [NSString stringWithFormat:@"PROXY: ON ⚡%d", (int)atomic_load(&gProxyHits)];
}

- (void)styleProxyBtn {
    UIColor *c = [DSProxy shared].enabled ? DSHex(kGreen) : DSHex(kDim);
    [_proxyBtn setTitle:[self proxyTitle] forState:UIControlStateNormal];
    [_proxyBtn setTitleColor:c forState:UIControlStateNormal]; _proxyBtn.tintColor = c;
    _proxyBtn.backgroundColor = [c colorWithAlphaComponent:0.10];
    _proxyBtn.layer.borderColor = [c colorWithAlphaComponent:0.5].CGColor;
}

- (void)proxyAlert:(NSString *)title msg:(NSString *)msg {
    UIAlertController *a = [UIAlertController alertControllerWithTitle:title message:msg preferredStyle:UIAlertControllerStyleAlert];
    [a addAction:[UIAlertAction actionWithTitle:@"حسناً" style:UIAlertActionStyleDefault handler:nil]];
    [self presentViewController:a animated:YES completion:nil];
}

- (void)proxyTap:(UIButton *)b {
    DSProxy *p = [DSProxy shared];
    if (!p.enabled && !p.host.length) { [self proxyLinkTap]; return; }   // لا يوجد رابط بعد
    p.enabled = !p.enabled; [p save]; [self styleProxyBtn];
    [self toast:p.enabled ? @"تم تشغيل البروكسي ✅ (للاتصالات الجديدة)" : @"تم إيقاف البروكسي"];
}

- (void)proxyRunTest {
    [self toast:@"⏳ جارٍ اختبار البروكسي…"];
    DSProxyTest(^(NSString *report, BOOL ok) { [self proxyAlert:(ok ? @"✅ البروكسي يعمل" : @"❌ فشل البروكسي") msg:report]; });
}

- (void)proxyApplyText:(NSString *)txt {
    NSString *err = nil;
    if (![[DSProxy shared] applyLink:txt error:&err]) { [self proxyAlert:@"❌ رابط غير صالح" msg:err ?: @"تعذّر قراءة الرابط"]; return; }
    [self styleProxyBtn];
    [self proxyRunTest];   // بعد الحفظ والتفعيل نختبره مباشرة
}

- (void)proxyLinkTap {
    DSProxy *p = [DSProxy shared];
    UIAlertController *a = [UIAlertController alertControllerWithTitle:@"🌐 رابط البروكسي"
        message:@"socks5://user:pass@host:1080\nhttp://host:8080\nhost:port  أو  host:port:user:pass\nرابط تيليجرام: t.me/socks?server=..&port=.." preferredStyle:UIAlertControllerStyleAlert];
    [a addTextFieldWithConfigurationHandler:^(UITextField *t) {
        t.placeholder = @"socks5://host:port"; t.text = p.link; t.font = DSMono(13, UIFontWeightRegular);
        t.keyboardType = UIKeyboardTypeURL; t.clearButtonMode = UITextFieldViewModeWhileEditing;
        t.autocapitalizationType = UITextAutocapitalizationTypeNone; t.autocorrectionType = UITextAutocorrectionTypeNo;
    }];
    __weak UIAlertController *wa = a;
    [a addAction:[UIAlertAction actionWithTitle:@"حفظ وتفعيل" style:UIAlertActionStyleDefault handler:^(UIAlertAction *x) {
        [self proxyApplyText:wa.textFields[0].text ?: @""];
    }]];
    [a addAction:[UIAlertAction actionWithTitle:@"📋 لصق من الحافظة وتفعيل" style:UIAlertActionStyleDefault handler:^(UIAlertAction *x) {
        [self proxyApplyText:UIPasteboard.generalPasteboard.string ?: @""];
    }]];
    if (p.host.length) {
        [a addAction:[UIAlertAction actionWithTitle:@"🗑 حذف البروكسي" style:UIAlertActionStyleDestructive handler:^(UIAlertAction *x) {
            p.enabled = NO; p.link = nil; p.host = nil; p.user = nil; p.pass = nil; p.port = 0; [p save];
            [self styleProxyBtn]; [self toast:@"تم حذف البروكسي"];
        }]];
    }
    [a addAction:[UIAlertAction actionWithTitle:@"إلغاء" style:UIAlertActionStyleCancel handler:nil]];
    [self presentViewController:a animated:YES completion:nil];
}

- (void)proxyTestTap {
    if (![DSProxy shared].host.length) { [self proxyLinkTap]; return; }
    [self proxyRunTest];
}

- (void)chatTap:(UIButton *)b {   // لحظي: يسري على أي اتصال جديد
    DSSettings *st = [DSSettings shared];
    st.chatMode = !st.chatMode; [st save];
    UIColor *c = st.chatMode ? DSHex(kGreen) : DSHex(kDim);
    [b setTitle:(st.chatMode ? @"CHAT → 8.8.8.8" : @"CHAT OFF") forState:UIControlStateNormal];
    [b setTitleColor:c forState:UIControlStateNormal]; b.tintColor = c;
    b.backgroundColor = [c colorWithAlphaComponent:0.12];
    b.titleLabel.adjustsFontSizeToFitWidth = YES; b.titleLabel.minimumScaleFactor = 0.7;
    [self toast:(st.chatMode ? @"الدردشة والكتابة → 8.8.8.8 💬" : @"الدردشة رجعت طبيعية")];
}

static NSString *DSFindJoinSoundFile(void);   // تصريح مسبق — التعريف الكامل لاحقاً بنفس الملف

- (void)joinSoundTap:(UIButton *)b {
    DSSettings *st = [DSSettings shared];
    st.joinSoundOn = !st.joinSoundOn; [st save];
    UIColor *c = st.joinSoundOn ? DSHex(kCyan) : DSHex(kDim);
    [b setTitle:(st.joinSoundOn ? @"JOIN SOUND: ON" : @"JOIN SOUND: OFF") forState:UIControlStateNormal];
    [b setTitleColor:c forState:UIControlStateNormal]; b.tintColor = c;
    b.backgroundColor = [c colorWithAlphaComponent:0.12];
    b.titleLabel.adjustsFontSizeToFitWidth = YES; b.titleLabel.minimumScaleFactor = 0.7;
    if (st.joinSoundOn && !DSFindJoinSoundFile())
        [self toast:@"⚠️ ضع ملف join.mp3 (أو wav/m4a/caf) داخل Documents/AflatoonSuite"];
    else
        [self toast:(st.joinSoundOn ? @"صوت الدخول مفعّل 🔊" : @"صوت الدخول متوقف")];
}

- (void)joinSpeedTap:(UIButton *)b {
    DSSettings *st = [DSSettings shared];
    int cur = (int)st.joinSoundRate; int next = cur + 1; if (next > 4) next = 1;
    st.joinSoundRate = (float)next; [st save];
    [b setTitle:[NSString stringWithFormat:@"SPEED x%d", next] forState:UIControlStateNormal];
    [self toast:[NSString stringWithFormat:@"سرعة صوت الدخول x%d", next]];
}

- (void)kbRepeatTap:(UIButton *)b {
    DSSettings *st = [DSSettings shared];
    st.kbRepeatNums = !st.kbRepeatNums; [st save];
    UIColor *c = st.kbRepeatNums ? DSHex(kAmber) : DSHex(kDim);
    [b setTitle:(st.kbRepeatNums ? @"تكرار الأرقام: ON" : @"تكرار الأرقام: OFF") forState:UIControlStateNormal];
    [b setTitleColor:c forState:UIControlStateNormal]; b.tintColor = c;
    b.backgroundColor = [c colorWithAlphaComponent:0.12]; b.layer.borderColor = [c colorWithAlphaComponent:0.5].CGColor;
    [self toast:(st.kbRepeatNums ? @"تكرار الأرقام مفعّل: 135 ← 135.135 🔁" : @"تكرار الأرقام متوقف")];
}

- (void)kbSplitTap:(UIButton *)b {
    DSSettings *st = [DSSettings shared];
    st.kbSplitLetters = !st.kbSplitLetters; [st save];
    UIColor *c = st.kbSplitLetters ? DSHex(kPurple) : DSHex(kDim);
    [b setTitle:(st.kbSplitLetters ? @"تفكيك الحروف: ON" : @"تفكيك الحروف: OFF") forState:UIControlStateNormal];
    [b setTitleColor:c forState:UIControlStateNormal]; b.tintColor = c;
    b.backgroundColor = [c colorWithAlphaComponent:0.12]; b.layer.borderColor = [c colorWithAlphaComponent:0.5].CGColor;
    [self toast:(st.kbSplitLetters ? @"تفكيك الحروف مفعّل: حسين ← ح س ي ن ✂️" : @"تفكيك الحروف متوقف")];
}

- (NSString *)kbSenseModeTitle {
    NSInteger m = [DSSettings shared].kbSenseMode;
    static const double fixed[] = {0, 0.05, 0.1, 0.2, 0.4};
    if (m <= 0 || m > 4) return @"الحساسية: ذكي AUTO";
    return [NSString stringWithFormat:@"الحساسية: %gs", fixed[m]];
}

- (void)kbStyle:(UIButton *)b title:(NSString *)t color:(UIColor *)c {
    [b setTitle:t forState:UIControlStateNormal];
    [b setTitleColor:c forState:UIControlStateNormal]; b.tintColor = c;
    b.backgroundColor = [c colorWithAlphaComponent:0.12]; b.layer.borderColor = [c colorWithAlphaComponent:0.5].CGColor;
    b.titleLabel.adjustsFontSizeToFitWidth = YES; b.titleLabel.minimumScaleFactor = 0.7;
}

- (void)dealloc { [[NSNotificationCenter defaultCenter] removeObserver:self]; }

- (void)digitSendTap:(UIButton *)b {   // إرسال تلقائي عند اكتمال N رقم (بديل «الاوجود»)
    DSDigitSendToggle();
    UIColor *c = DSDigitSendIsOn() ? DSHex(kGreen) : DSHex(kDim);
    [b setTitle:DSDigitSendTitle() forState:UIControlStateNormal];
    [b setTitleColor:c forState:UIControlStateNormal]; b.tintColor = c;
    b.backgroundColor = [c colorWithAlphaComponent:0.12]; b.layer.borderColor = [c colorWithAlphaComponent:0.5].CGColor;
    [self toast:(DSDigitSendIsOn() ? [NSString stringWithFormat:@"لما تكتب %ld رقم بحقل دردشة اللعبة (أو الكتابة السريعة) تنرسل تلقائياً. العدد يتغير من قائمة ULTRA", (long)DSDigitSendN()]
                                   : @"الإرسال عند اكتمال الأرقام متوقف")];
}

- (NSString *)liveTitle {
    DSSettings *st = [DSSettings shared];
    return st.liveSpeedOn ? [NSString stringWithFormat:@"السرعة الحية: ON  (x%g)", (double)st.liveSpeed] : @"السرعة الحية: OFF";
}

- (void)liveSync {   // المنيو الصغير أغلق الخيار → حدّث زر القائمة
    [self kbStyle:_liveBtn title:[self liveTitle] color:([DSSettings shared].liveSpeedOn ? DSHex(kPurple) : DSHex(kDim))];
}

- (NSString *)gsTitle {
    BOOL on = [NSUserDefaults.standardUserDefaults boolForKey:@"DSGameSpeedOn"];
    return on ? [NSString stringWithFormat:@"تسريع اللعبة (X8): ON  (x%g)", DSGSGetScale()] : @"تسريع اللعبة (X8): OFF";
}

- (void)gsSync {   // المنيو الصغير تغيّر → حدّث زر القائمة
    BOOL on = [NSUserDefaults.standardUserDefaults boolForKey:@"DSGameSpeedOn"];
    [self kbStyle:_gsBtn title:[self gsTitle] color:(on ? DSHex(kAmber) : DSHex(kDim))];
}

- (void)gsTap:(UIButton *)b {
    NSUserDefaults *d = NSUserDefaults.standardUserDefaults;
    BOOL on = ![d boolForKey:@"DSGameSpeedOn"];
    [d setBool:on forKey:@"DSGameSpeedOn"];
    if (on) DSGSShow();
    else { DSGSSetScale(1.0); DSGSApplyLayerSpeed(); DSGSHide(); }
    [self gsSync];
    [self toast:(on ? @"ظهر منيو تسريع اللعبة — اختر x2/x3/x4 ⏩ (يبدأ دائماً من x1 عند فتح التطبيق)" : @"تسريع اللعبة متوقف")];
}

- (void)liveSpeedTap:(UIButton *)b {
    DSSettings *st = [DSSettings shared];
    st.liveSpeedOn = !st.liveSpeedOn; [st save];
    gLiveLiveGen++;
    if (st.liveSpeedOn) DSLiveShow(); else DSLiveHide();
    DSLiveApplyMedia();
    [self liveSync];
    [self toast:(st.liveSpeedOn ? @"ظهر منيو صغير: اختر x2/x3/x4 — البث الحي يجمع تأخيراً ثم يلحق 🎚️" : @"السرعة الحية متوقفة")];
}

- (void)kbSenseTap:(UIButton *)b {
    DSSettings *st = [DSSettings shared];
    st.kbSense = !st.kbSense; [st save];
    DSKbResetSense();
    [self kbStyle:b title:(st.kbSense ? @"حساسية الكيبورد: ON" : @"حساسية الكيبورد: OFF") color:(st.kbSense ? DSHex(kGreen) : DSHex(kDim))];
    [self toast:(st.kbSense ? @"حساسية الكيبورد مفعّلة: لا يرسل وأنت تكتب، ويرسل لما ترفع يدك 👆" : @"حساسية الكيبورد متوقفة")];
}

- (void)kbSenseModeTap:(UIButton *)b {
    DSSettings *st = [DSSettings shared];
    st.kbSenseMode = (st.kbSenseMode + 1) % 5; [st save];
    DSKbResetSense();
    [self kbStyle:b title:[self kbSenseModeTitle] color:DSHex(kCyan)];
    [self toast:(st.kbSenseMode == 0 ? @"ذكاء AUTO: يتعلّم إيقاع كتابتك ويصحّح نفسه، يرسل فور توقفك 🧠" : [NSString stringWithFormat:@"يرسل بعد %@ من رفع اليد", [[self kbSenseModeTitle] substringFromIndex:10]])];
}

- (void)kbMinCharsTap:(UIButton *)b {
    DSSettings *st = [DSSettings shared];
    static const NSInteger opts[] = {1, 2, 3, 4, 6, 8}; int n = 6, next = 0;
    for (int i = 0; i < n; i++) if (opts[i] > st.kbMinChars) { next = i; break; }
    st.kbMinChars = opts[next]; [st save];
    [self kbStyle:b title:[NSString stringWithFormat:@"أقل عدد أحرف: %ld", (long)opts[next]] color:DSHex(kAmber)];
    [self toast:[NSString stringWithFormat:@"لا يرسل إلا إذا كتبت %ld أحرف أو أكثر", (long)opts[next]]];
}

- (void)kbHapticTap:(UIButton *)b {
    DSSettings *st = [DSSettings shared];
    st.kbHaptic = !st.kbHaptic; [st save];
    [self kbStyle:b title:(st.kbHaptic ? @"اهتزاز عند الارسال: ON" : @"اهتزاز عند الارسال: OFF") color:(st.kbHaptic ? DSHex(kPurple) : DSHex(kDim))];
    [self toast:(st.kbHaptic ? @"اهتزاز خفيف عند كل إرسال 📳" : @"الاهتزاز متوقف")];
}

- (void)quickModesTap:(UIButton *)b {   // أوضاع الكيبورد (أرقام/عكس/أسماء/تفكيك) على رسائل «الكتابة السريعة»
    DSQuickModesToggle();
    [b setTitle:DSQuickModesTitle() forState:UIControlStateNormal];
    UIColor *c = DSQuickModesOn() ? DSHex(kGreen) : DSHex(kDim);
    [b setTitleColor:c forState:UIControlStateNormal]; b.tintColor = c;
    [self toast:(DSQuickModesOn() ? @"رسائل الكتابة السريعة تمر على الأوضاع المفعّلة (أرقام/عكس/أسماء/تفكيك) قبل الإرسال للعبة"
                                  : @"الكتابة السريعة ترسل نصك كما هو بدون أوضاع")];
}

- (NSString *)pingTitle { return [DSSettings shared].pingOn ? @"PING على الشاشة: ON" : @"PING على الشاشة: OFF"; }

- (void)pingTap:(UIButton *)b {
    DSSettings *st = [DSSettings shared];
    st.pingOn = !st.pingOn; [st save];
    if (st.pingOn) DSPingShow(); else DSPingHide();
    UIColor *c = st.pingOn ? DSHex(kGreen) : DSHex(kDim);
    [b setTitle:[self pingTitle] forState:UIControlStateNormal];
    [b setTitleColor:c forState:UIControlStateNormal]; b.tintColor = c;
    b.backgroundColor = [c colorWithAlphaComponent:0.12]; b.layer.borderColor = [c colorWithAlphaComponent:0.5].CGColor;
    [self toast:(st.pingOn ? @"ظهر PING فوق الشاشة (يتحدّث كل ثانية ونصف). اسحبه لأي مكان، واضغطه ليبدّل الهدف: Cloudflare ← Google ← سيرفر اللعبة 📶" : @"PING متوقف")];
}

- (NSString *)ntgTitle {
    return DS_NTG_LINKED ? @"NTgCalls: مرتبطة بالأداة" : @"NTgCalls: غير مرتبطة";
}

// حالياً زر حالة فقط: يوضح هل رُبطت المكتبة وقت البناء. الدوال الفعلية تُضاف بعد قراءة ntgcalls.h.
- (void)ntgTap:(UIButton *)b {
#if DS_HAS_NTGCALLS
    [self toast:@"مكتبة NTgCalls مرتبطة بهذي النسخة. الخيارات الفعلية (دخول مكالمة، بث صوت) تنضاف بعد قراءة ntgcalls.h."];
#else
    [self toast:@"NTgCalls غير مرتبطة. شغّل ملف build-ntgcalls-ios.yml بـ GitHub Actions، ثم ضع libntgcalls.a داخل libs/ وملف ntgcalls.h داخل libs/include/ وأعد البناء."];
#endif
}

- (void)forceZegoTap:(UIButton *)b {
    DSForceZegoOnlyCycle();
    BOOL on = DSForceZegoOnlyIsOn();
    UIColor *c = on ? DSHex(kRed) : DSHex(kDim);
    [b setTitle:DSForceZegoOnlyTitle() forState:UIControlStateNormal];
    [b setTitleColor:c forState:UIControlStateNormal]; b.tintColor = c;
    b.backgroundColor = [c colorWithAlphaComponent:0.12]; b.layer.borderColor = [c colorWithAlphaComponent:0.5].CGColor;
    [self toast:(on ? @"⚠️ Agora ممنوع الآن من الانضمام لأي قناة. إذا ما كان عند اللعبة مسار بديل لهذي الغرفة، الصوت بينقطع كلياً — جرّب بروم صوتي واحد وراقب النتيجة." : @"فرض Zego فقط متوقف — Agora يشتغل عادي")];
}

- (void)lowLatTap:(UIButton *)b {   // يدور: OFF ← خفيف ← قوي ← أقصى (تقليل تأخير صوت الروم)
    DSAgoraLowLatCycle();
    [b setTitle:DSAgoraLowLatTitle() forState:UIControlStateNormal];
    [b setTitleColor:(DSAgoraLowLatIsOn() ? DSHex(kGreen) : DSHex(kDim)) forState:UIControlStateNormal];
    if (!DSAgoraLowLatIsOn()) { [self toast:@"للرجوع للإعدادات الأصلية أعد فتح اللعبة"]; return; }
    if (DSAgoraLowLat() >= 5) {
        [self toast:(gDSKeyAll > 0 ? [NSString stringWithFormat:@"Agora: قبل %d من %d — Zego (7 مفاتيح) تحتاج إعادة فتح اللعبة", gDSKeyOK, gDSKeyAll]
                                   : @"Agora: يُطبَّق أول ما تدخل روم صوت — Zego (7 مفاتيح) تحتاج إعادة فتح اللعبة")];
        return;
    }
    [self toast:(gDSKeyAll > 0 ? [NSString stringWithFormat:@"قبلها Agora: %d من %d مفتاح — إذا ما حسّيت فرق اخرج وادخل الروم", gDSKeyOK, gDSKeyAll]
                               : @"يُطبَّق أول ما تدخل روم صوت")];
}

- (void)audioProTap:(UIButton *)b {   // يفتح القائمة الثالثة: Audio PRO
    DSAudioProVC *vc = [DSAudioProVC new];
    vc.modalPresentationStyle = UIModalPresentationFullScreen;
    [self presentViewController:vc animated:YES completion:nil];
}

- (void)ultraTap:(UIButton *)b {   // يفتح القائمة الثانية
    DSUltraVC *vc = [DSUltraVC new];
    vc.modalPresentationStyle = UIModalPresentationFullScreen;
    [self presentViewController:vc animated:YES completion:nil];
}

- (void)kbNumTap:(UIButton *)b {   // OFF ← ترتيب ← تدبيل ← تدبيل الأخير
    DSKbNumCycle();
    [b setTitle:DSKbNumTitle() forState:UIControlStateNormal];
    [b setTitleColor:(DSKbNumIsOn() ? DSHex(kAmber) : DSHex(kDim)) forState:UIControlStateNormal];
    NSInteger m = [NSUserDefaults.standardUserDefaults integerForKey:@"DSKbNum"];
    [self toast:(m == 1 ? @"ترتيب الأرقام: 938747 ← 938 747"
               : m == 2 ? @"تدبيل: 929818 ← 929 929 818 818"
               : m == 3 ? @"تدبيل آخر مرتبة: 938100 ← 938 100 100"
                        : @"أوضاع الأرقام متوقفة")];
}

- (void)kbRevTap:(UIButton *)b {
    DSKbRevToggle();
    [b setTitle:DSKbRevTitle() forState:UIControlStateNormal];
    [b setTitleColor:(DSKbRevIsOn() ? DSHex(kPurple) : DSHex(kDim)) forState:UIControlStateNormal];
    [self toast:(DSKbRevIsOn() ? @"عكس الرسالة مفعّل: هلو ← وله (يعمل مع أي وضع)" : @"عكس الرسالة متوقف")];
}

- (void)kbNamesTap:(UIButton *)b {
    DSKbNamesToggle();
    [b setTitle:DSKbNamesTitle() forState:UIControlStateNormal];
    [b setTitleColor:(DSKbNamesIsOn() ? DSHex(kGreen) : DSHex(kDim)) forState:UIControlStateNormal];
    [self toast:(DSKbNamesIsOn() ? @"أسماء بحرف: اكتب حرف واحد بحقل فاضي وتطلع أسماء الفئات المفعّلة" : @"أسماء بحرف متوقف")];
}

- (void)kbCatsTap:(UIButton *)b {
    UIAlertController *a = [UIAlertController alertControllerWithTitle:@"فئات الأسماء" message:@"اضغط على فئة لتشغيلها أو إيقافها" preferredStyle:UIAlertControllerStyleAlert];
    for (int i = 0; i < 6; i++) {
        BOOL on = (DSKbCatsMask() >> i) & 1;
        [a addAction:[UIAlertAction actionWithTitle:[NSString stringWithFormat:@"%@ %@", on ? @"✓" : @"✗", DSKbCatName(i)] style:UIAlertActionStyleDefault handler:^(UIAlertAction *x) {
            DSKbCatsToggleBit(i);
            dispatch_after(dispatch_time(DISPATCH_TIME_NOW, 150 * NSEC_PER_MSEC), dispatch_get_main_queue(), ^{ [self kbCatsTap:b]; });
        }]];
    }
    [a addAction:[UIAlertAction actionWithTitle:@"تم" style:UIAlertActionStyleCancel handler:nil]];
    [self presentViewController:a animated:YES completion:nil];
}

- (void)agoraAdvTap:(UIButton *)b {   // OFF ← زمن أقل ← زمن أقل + بدون معالجة
    DSAgoraAdvCycle();
    [b setTitle:DSAgoraAdvTitle() forState:UIControlStateNormal];
    [b setTitleColor:(DSAgoraAdvIsOn() ? DSHex(kGreen) : DSHex(kDim)) forState:UIControlStateNormal];
    NSInteger m = [NSUserDefaults.standardUserDefaults integerForKey:@"DSAgoraAdv"];
    [self toast:(m == 1 ? @"Agora: مخازن التشغيل على 0 + تسريع NetEQ + low-latency. يُطبَّق على روم الصوت الحالي"
               : m == 2 ? @"أيضاً أوقفت AEC/AGC/NS/كشف الصفير. انتبه: قد يرجع صدى بدون سماعات"
                        : @"للرجوع الكامل للإعدادات الأصلية اخرج وادخل الروم (أو أعد فتح اللعبة)")];
}

- (void)audioGainTap:(UIButton *)b {   // يدور: OFF ← x1.5 ← x2 ← x3 ← x4
    DSAudioGainCycle();
    [b setTitle:DSAudioGainTitle() forState:UIControlStateNormal];
    [b setTitleColor:(DSAudioGainIsOn() ? DSHex(kGreen) : DSHex(kDim)) forState:UIControlStateNormal];
    if (!DSAudioGainIsOn()) { [self toast:@"التقوية متوقفة — الصوت رجع للأصل"]; return; }
    [self toast:(gDSAgoraGainOK ? @"Agora: التقوية مطبّقة على صوت الروم، وباقي الأصوات (Zego/اللعبة) تتقوى على المخرج. إذا انخفض الوضوح أو سمعت تشويه نزّل مستوى."
                               : @"تتقوى أصوات اللعبة وZego فوراً على المخرج، وAgora يُطبَّق أول ما تدخل روم صوت. إذا سمعت تشويه نزّل مستوى.")];
}

- (void)audioQoSTap:(UIButton *)b {   // OFF ← الصوت ← كل اللعبة
    DSAudioQoSToggle();
    [b setTitle:DSAudioQoSTitle() forState:UIControlStateNormal];
    [b setTitleColor:(DSAudioQoSIsOn() ? DSHex(kGreen) : DSHex(kDim)) forState:UIControlStateNormal];
    NSInteger m = DSAudioQoSMode();
    [self toast:(m == 0 ? @"أولوية QoS متوقفة — الاتصالات والخيوط الجديدة ترجع عادية (للرجوع الكامل أعد فتح اللعبة)"
               : m == 1 ? @"QoS الصوت: UDP بفئة «صوت» + رفع خيوط Agora/Zego. اخرج وادخل الروم ليشمل الاتصال الجديد"
                        : @"QoS كل اللعبة: UDP صوت + TCP تفاعلي + HTTP/WebSocket + خيوط اللعبة والصوت. الأفضل تعيد فتح اللعبة ليشمل الخيوط الشغّالة")];
}

- (void)audioBufTap:(UIButton *)b {   // OFF ← 5ms ← 2.5ms
    DSAudioBufCycle();
    [b setTitle:DSAudioBufTitle() forState:UIControlStateNormal];
    [b setTitleColor:(DSAudioBufIsOn() ? DSHex(kGreen) : DSHex(kDim)) forState:UIControlStateNormal];
    [self toast:(DSAudioBufIsOn() ? @"طلبت مخزن أصغر للجهاز — النظام يقرّبه لأقرب قيمة يدعمها (قد يسبب تقطيع بالأجهزة الضعيفة، رجّعه OFF لو حسّيت)"
                                  : @"للرجوع للمخزن الأصلي أعد فتح اللعبة")];
}

- (void)flagTap:(UIButton *)b {   // يظهر/يخفي الزر العائم 🚩 (الاختيار بالداخل: اسم الدولة أو العاصمة)
    BOOL on = !DSFlagBubbleIsOn();
    DSFlagSetBubble(on);
    [b setTitle:(on ? @"الدول (علم ← اسم/عاصمة): ON" : @"الدول (علم ← اسم/عاصمة): OFF") forState:UIControlStateNormal];
    [b setTitleColor:(on ? DSHex(kGreen) : DSHex(kDim)) forState:UIControlStateNormal];
    [self toast:(on ? @"ظهر الزر 🚩 — اضغطه واختر: اسم الدولة أو العاصمة" : @"زر الدول مخفي (الاختيار محفوظ)")];
}

- (void)quickSendTap:(UIButton *)b {
    DSSettings *st = [DSSettings shared];
    BOOL on = !st.quickSendOn;
    st.quickSendOn = on; [st save];
    [b setTitle:(on ? @"الكتابة السريعة: ON" : @"الكتابة السريعة: OFF") forState:UIControlStateNormal];
    [b setTitleColor:(on ? DSHex(kGreen) : DSHex(kDim)) forState:UIControlStateNormal];
    if (on) { DSQuickShow(); [self toast:@"فتحت الكتابة السريعة — تكتب وتضغط إرسال، تذهب لآخر حقل دردشة فتحته 📝"]; }
    else { DSQuickHide(); [self toast:@"الكتابة السريعة متوقفة"]; }
}

- (void)voiceSpeedTap:(UIButton *)b {
    DSSettings *st = [DSSettings shared];
    st.voiceSpeedOn = !st.voiceSpeedOn; [st save];
    UIColor *c = st.voiceSpeedOn ? DSHex(kPurple) : DSHex(kDim);
    [b setTitle:(st.voiceSpeedOn ? @"VOICE SPEED: ON" : @"VOICE SPEED: OFF") forState:UIControlStateNormal];
    [b setTitleColor:c forState:UIControlStateNormal]; b.tintColor = c;
    b.backgroundColor = [c colorWithAlphaComponent:0.12];
    b.titleLabel.adjustsFontSizeToFitWidth = YES; b.titleLabel.minimumScaleFactor = 0.7;
    [self toast:(st.voiceSpeedOn ? @"سرعة صوت المتكلمين مفعّلة 🎙️" : @"سرعة صوت المتكلمين متوقفة")];
}

- (void)voiceSpeedMaxTap:(UIButton *)b {
    DSSettings *st = [DSSettings shared];
    int cur = (int)st.voiceSpeedMax; int next = cur + 1; if (next > 4) next = 1;
    st.voiceSpeedMax = (float)next; [st save];
    [b setTitle:[NSString stringWithFormat:@"MAX x%d", next] forState:UIControlStateNormal];
    [self toast:[NSString stringWithFormat:@"الحد الأقصى للتسريع x%d", next]];
}

- (void)rulesTap {
    DSRulesVC *vc = [[DSRulesVC alloc] initWithStyle:UITableViewStyleInsetGrouped];
    UINavigationController *nav = [[UINavigationController alloc] initWithRootViewController:vc];
    nav.overrideUserInterfaceStyle = UIUserInterfaceStyleDark;
    [self presentViewController:nav animated:YES completion:nil];
}

- (void)serverTestTap {
    DSTestVC *vc = [DSTestVC new];
    UINavigationController *nav = [[UINavigationController alloc] initWithRootViewController:vc];
    nav.overrideUserInterfaceStyle = UIUserInterfaceStyleDark;
    [self presentViewController:nav animated:YES completion:nil];
}

- (void)apiTap {
    DSSettings *st = [DSSettings shared];
    UIAlertController *a = [UIAlertController alertControllerWithTitle:@"🔑 NextDNS"
        message:@"مفتاح API من my.nextdns.io/account\nProfile ID اختياري (يُكتشف تلقائياً)" preferredStyle:UIAlertControllerStyleAlert];
    [a addTextFieldWithConfigurationHandler:^(UITextField *t) {
        t.placeholder = st.apiKey.length ? @"•••••• (محفوظ — اتركه فارغاً للإبقاء)" : @"API Key";
        t.autocapitalizationType = UITextAutocapitalizationTypeNone; t.autocorrectionType = UITextAutocorrectionTypeNo;
    }];
    [a addTextFieldWithConfigurationHandler:^(UITextField *t) {
        t.placeholder = @"Profile ID (اختياري)"; t.text = st.profileId;
        t.autocapitalizationType = UITextAutocapitalizationTypeNone; t.autocorrectionType = UITextAutocorrectionTypeNo;
    }];
    __weak UIAlertController *wa = a;
    [a addAction:[UIAlertAction actionWithTitle:@"إلغاء" style:UIAlertActionStyleCancel handler:nil]];
    [a addAction:[UIAlertAction actionWithTitle:@"حذف المفتاح" style:UIAlertActionStyleDestructive handler:^(UIAlertAction *x) {
        st.apiKey = nil; st.profileId = nil; [st save]; [self toast:@"تم حذف المفتاح"];
    }]];
    [a addAction:[UIAlertAction actionWithTitle:@"حفظ" style:UIAlertActionStyleDefault handler:^(UIAlertAction *x) {
        NSCharacterSet *ws = NSCharacterSet.whitespaceAndNewlineCharacterSet;
        NSString *k = [wa.textFields[0].text stringByTrimmingCharactersInSet:ws];
        NSString *p = [wa.textFields[1].text stringByTrimmingCharactersInSet:ws];
        if (k.length) st.apiKey = k;
        if (![p isEqualToString:st.profileId ?: @""] || k.length) st.profileId = p.length ? p : nil;
        [st save];
        if (!st.apiKey.length) { [self toast:@"لا يوجد مفتاح"]; return; }
        [self toast:@"جاري التحقق…"];
        DSNDEnsureProfile(^(NSString *pid, NSString *err) {
            [self toast:pid ? @"تم الحفظ والتحقق ✅" : err];
        });
    }]];
    [self presentViewController:a animated:YES completion:nil];
}

- (void)blockDomain:(NSString *)d {
    DSSettings *st = [DSSettings shared];
    if (!st.apiKey.length) { [self toast:@"أدخل مفتاح API أولاً"]; [self apiTap]; return; }
    [self toast:@"جاري الإرسال…"];
    DSNDEnsureProfile(^(NSString *pid, NSString *err) {
        if (!pid) { [self toast:err]; return; }
        NSString *path = [NSString stringWithFormat:@"/profiles/%@/denylist", pid];
        DSNDRequest(@"POST", path, @{ @"id": d, @"active": @YES }, ^(NSInteger code, id json, NSError *e) {
            if (code / 100 == 2) { [st markSent:d]; [self toast:[NSString stringWithFormat:@"⛔ تم حجب %@", d]]; [self reload]; }
            else if (code == 409 || [DSNDErrorText(code, json) containsString:@"duplicate"]) { [st markSent:d]; [self toast:@"موجود مسبقاً في Denylist"]; [self reload]; }
            else if (code == 401 || code == 403) [self toast:@"مفتاح API غير صحيح"];
            else [self toast:e ? e.localizedDescription : DSNDErrorText(code, json)];
        });
    });
}

- (void)showActionsFor:(NSDictionary *)e from:(UIView *)src {
    NSString *v = e[@"value"];
    BOOL isDomain = [e[@"type"] isEqualToString:@"domain"];
    UIAlertController *a = [UIAlertController alertControllerWithTitle:v message:nil preferredStyle:UIAlertControllerStyleActionSheet];
    if (isDomain) {
        [a addAction:[UIAlertAction actionWithTitle:@"⛔ حجب (NextDNS)" style:UIAlertActionStyleDestructive handler:^(UIAlertAction *x) { [self blockDomain:v]; }]];
    } else {
        NSUInteger n = 0;
        for (NSString *r in e[@"related"]) {
            if (DSIsIPString(r) || n++ >= 3) continue;
            [a addAction:[UIAlertAction actionWithTitle:[@"⛔ حجب " stringByAppendingString:r] style:UIAlertActionStyleDestructive handler:^(UIAlertAction *x) { [self blockDomain:r]; }]];
        }
    }
    [a addAction:[UIAlertAction actionWithTitle:@"🔁 استبدال…" style:UIAlertActionStyleDefault handler:^(UIAlertAction *x) {
        [DSRulesVC promptFrom:v over:self done:^{ [self toast:@"تمت إضافة القاعدة ✅"]; }];
    }]];
    [a addAction:[UIAlertAction actionWithTitle:@"📋 نسخ" style:UIAlertActionStyleDefault handler:^(UIAlertAction *x) {
        UIPasteboard.generalPasteboard.string = v; [self toast:@"تم النسخ"];
    }]];
    [a addAction:[UIAlertAction actionWithTitle:@"إلغاء" style:UIAlertActionStyleCancel handler:nil]];
    a.popoverPresentationController.sourceView = src;
    a.popoverPresentationController.sourceRect = src.bounds;
    [self presentViewController:a animated:YES completion:nil];
}

- (void)saveTap {
    [[DSStore shared] saveAll];
    UIAlertController *a = [UIAlertController alertControllerWithTitle:@"تم الحفظ ✅"
        message:@"Documents/AflatoonSuite/\n• denylist_nextdns.txt\n• domains.txt\n• ips.txt\n• data.json\n\nاستخدم زر SHARE لحفظها في تطبيق الملفات."
        preferredStyle:UIAlertControllerStyleAlert];
    [a addAction:[UIAlertAction actionWithTitle:@"حسناً" style:UIAlertActionStyleDefault handler:nil]];
    [self presentViewController:a animated:YES completion:nil];
}

- (void)shareTap:(UIButton *)sender {
    NSArray *urls = [[DSStore shared] saveAll];
    UIActivityViewController *vc = [[UIActivityViewController alloc] initWithActivityItems:urls applicationActivities:nil];
    vc.popoverPresentationController.sourceView = sender;
    vc.popoverPresentationController.sourceRect = sender.bounds;
    [self presentViewController:vc animated:YES completion:nil];
}

- (void)copyTap {
    UIPasteboard.generalPasteboard.string = [[DSStore shared] denylistText];
    [self toast:[NSString stringWithFormat:@"تم نسخ %lu نطاق", (unsigned long)[[DSStore shared] denylistCount]]];
}

- (void)clearTap {
    UIAlertController *a = [UIAlertController alertControllerWithTitle:@"مسح كل السجل؟" message:nil preferredStyle:UIAlertControllerStyleAlert];
    [a addAction:[UIAlertAction actionWithTitle:@"إلغاء" style:UIAlertActionStyleCancel handler:nil]];
    [a addAction:[UIAlertAction actionWithTitle:@"مسح" style:UIAlertActionStyleDestructive handler:^(UIAlertAction *x) {
        [[DSStore shared] clear]; [self reload];
    }]];
    [self presentViewController:a animated:YES completion:nil];
}

- (NSInteger)tableView:(UITableView *)tv numberOfRowsInSection:(NSInteger)s {
    if (_data.count == 0) {
        UILabel *l = [UILabel new]; l.numberOfLines = 0; l.textAlignment = NSTextAlignmentCenter;
        l.text = @"$ waiting for traffic…\nشغّل اللعبة وراح تظهر الاتصالات هنا";
        l.font = DSMono(12, UIFontWeightRegular); l.textColor = DSHex(kDim); tv.backgroundView = l;
    } else tv.backgroundView = nil;
    return _data.count;
}

- (UITableViewCell *)tableView:(UITableView *)tv cellForRowAtIndexPath:(NSIndexPath *)ip {
    DSCell *c = [tv dequeueReusableCellWithIdentifier:@"c" forIndexPath:ip];
    NSDictionary *e = _data[ip.row];
    [c configure:e sent:[[DSSettings shared] wasSent:e[@"value"]]];
    return c;
}

- (void)tableView:(UITableView *)tv didSelectRowAtIndexPath:(NSIndexPath *)ip {
    [tv deselectRowAtIndexPath:ip animated:YES];
    [self showActionsFor:_data[ip.row] from:[tv cellForRowAtIndexPath:ip]];
}
@end

#pragma mark - Floating orb

@interface DSPassWindow : UIWindow
@end
@implementation DSPassWindow
- (UIView *)hitTest:(CGPoint)p withEvent:(UIEvent *)e {
    UIView *v = [super hitTest:p withEvent:e];
    return (v == self.rootViewController.view || v == self) ? nil : v;
}
@end

@interface DSRootVC : UIViewController
@end
@implementation DSRootVC {
    UIButton *_fab; UIView *_ring; UILabel *_banner;
}
- (void)viewDidLoad {
    [super viewDidLoad];
    self.view.backgroundColor = UIColor.clearColor;
    _ring = [[UIView alloc] initWithFrame:CGRectMake(16, 140, 56, 56)];
    _ring.layer.cornerRadius = 28; _ring.layer.borderWidth = 1.5; _ring.layer.borderColor = DSHex(kGreen).CGColor;
    _ring.userInteractionEnabled = NO; [self.view addSubview:_ring];
    _fab = [UIButton buttonWithType:UIButtonTypeCustom];
    _fab.frame = CGRectMake(16, 140, 56, 56);
    _fab.backgroundColor = [DSHex(kBG) colorWithAlphaComponent:0.94];
    _fab.layer.cornerRadius = 28; _fab.layer.borderWidth = 1.5; _fab.layer.borderColor = DSHex(kGreen).CGColor;
    DSGlow(_fab.layer, DSHex(kGreen), 10);
    [_fab setImage:DSIcon(@"dot.radiowaves.left.and.right", 22) forState:UIControlStateNormal]; _fab.tintColor = DSHex(kGreen);
    [_fab addTarget:self action:@selector(open) forControlEvents:UIControlEventTouchUpInside];
    [_fab addGestureRecognizer:[[UIPanGestureRecognizer alloc] initWithTarget:self action:@selector(pan:)]];
    [self.view addSubview:_fab];
    [[NSNotificationCenter defaultCenter] addObserver:self selector:@selector(startPulse) name:UIApplicationDidBecomeActiveNotification object:nil];
}
- (void)startPulse {
    [_ring.layer removeAllAnimations];
    CABasicAnimation *s = [CABasicAnimation animationWithKeyPath:@"transform.scale"]; s.fromValue = @1; s.toValue = @1.7;
    CABasicAnimation *o = [CABasicAnimation animationWithKeyPath:@"opacity"]; o.fromValue = @0.7; o.toValue = @0;
    CAAnimationGroup *g = [CAAnimationGroup animation]; g.animations = @[s, o]; g.duration = 1.8; g.repeatCount = HUGE_VALF;
    [_ring.layer addAnimation:g forKey:@"pulse"];
}
- (void)viewDidAppear:(BOOL)animated {
    [super viewDidAppear:animated];
    [self startPulse];
    if (_banner) return;
    _banner = [UILabel new]; _banner.text = @"  ◉ AFLATOON SUITE  •  © أفلاطون / Aflatoon  ";
    _banner.font = DSMono(11, UIFontWeightBold); _banner.textColor = DSHex(kGreen); _banner.backgroundColor = [DSHex(kBG) colorWithAlphaComponent:0.95];
    _banner.layer.cornerRadius = 12; _banner.layer.borderWidth = 1; _banner.layer.borderColor = DSHex(kGreen).CGColor; _banner.clipsToBounds = YES;
    [_banner sizeToFit];
    CGFloat bw = _banner.bounds.size.width + 8, bh = 26;
    _banner.frame = CGRectMake((self.view.bounds.size.width - bw) / 2, self.view.safeAreaInsets.top + 6, bw, bh);
    _banner.textAlignment = NSTextAlignmentCenter; _banner.alpha = 0;
    [self.view addSubview:_banner];
    [UIView animateWithDuration:0.35 animations:^{ self->_banner.alpha = 1; } completion:^(BOOL f) {
        [UIView animateWithDuration:0.6 delay:3.0 options:0 animations:^{ self->_banner.alpha = 0; } completion:nil];
    }];
}
- (void)viewDidLayoutSubviews {
    [super viewDidLayoutSubviews];
    CGRect b = self.view.bounds; CGPoint c = _fab.center;
    c.x = MIN(MAX(c.x, 28), b.size.width - 28); c.y = MIN(MAX(c.y, 28), b.size.height - 28);
    _fab.center = c; _ring.center = c;
}
- (void)pan:(UIPanGestureRecognizer *)g {
    CGPoint t = [g translationInView:self.view];
    _fab.center = CGPointMake(_fab.center.x + t.x, _fab.center.y + t.y); _ring.center = _fab.center;
    [g setTranslation:CGPointZero inView:self.view];
    [self.view setNeedsLayout];
}
- (void)open {
    if (self.presentedViewController) return;
    DSMenuVC *vc = [DSMenuVC new];
    vc.modalPresentationStyle = UIModalPresentationFullScreen;
    [self presentViewController:vc animated:YES completion:nil];
}
@end

#pragma mark - تسريع صوت الروم مع الحفاظ على النغمة (WSOLA)
// ملاحظة مهمة: الدردشة حيّة وليست ملفاً جاهزاً. السرعة "تتكيّف" حسب التراكم المتوفر فقط —
// تبدأ من 1x وتتصاعد تدريجياً حتى الحد الأقصى المختار كلما وُجد تراكم (بعد وقفات الكلام مثلاً)،
// وتهدأ تلقائياً عند نفاد التراكم. هذا السلوك مُختبَر ومؤكد رياضياً (محرك overlap-add قياسي)،
// وليس تخميناً. تمت تجربة النواة بمعزل عن اللعبة قبل الدمج هنا.
#define DS_WS_CAP (48000 * 8)

typedef struct {
    int16_t ring[DS_WS_CAP]; long wpos, rpos;
    int sr, Hs, win, search;
    float accum[2048];
    long anaPos;
    int16_t prevTail[1024];
    int primed;
} DSWsola;

static void DSWsInit(DSWsola *w, int sr) {
    memset(w, 0, sizeof *w);
    w->sr = sr; w->Hs = sr / 100; w->win = w->Hs * 2; w->search = w->Hs / 2;
}
static void DSWsFeed(DSWsola *w, const int16_t *in, int n) {
    for (int i = 0; i < n; i++) w->ring[(w->wpos + i) % DS_WS_CAP] = in[i];
    w->wpos += n;
    if (w->wpos - w->rpos > DS_WS_CAP - 4096) w->rpos = w->wpos - (DS_WS_CAP - 4096);
}
static int16_t DSWsAt(DSWsola *w, long pos) { return (pos < w->rpos || pos >= w->wpos) ? 0 : w->ring[pos % DS_WS_CAP]; }

static int DSWsBestOffset(DSWsola *w, long candidate, const int16_t *ref, int refLen) {
    long bestScore = -1; int best = 0;
    for (int off = -w->search; off <= w->search; off++) {
        long start = candidate + off;
        if (start < w->rpos || start + refLen >= w->wpos) continue;
        long score = 0;
        for (int i = 0; i < refLen; i++) { int32_t a = ref[i], b = DSWsAt(w, start + i); score += a * b; }
        if (score > bestScore) { bestScore = score; best = off; }
    }
    return best;
}

// ينتج Hs عيّنة نهائية في كل نداء (نفس عدد العيّنات المطلوب من Agora)؛ السرعة تتكيّف تلقائياً
static void DSWsStep(DSWsola *w, int16_t *outHs, float maxSpeed) {
    if (w->Hs <= 0 || w->Hs > 1024) return;
    long avail = w->wpos - w->anaPos;
    float backlogSec = (float)avail / w->sr;
    float speed = 1.0f + (maxSpeed - 1.0f) * fminf(backlogSec / 1.0f, 1.0f);
    int Ha = (int)(w->Hs * speed); if (Ha < w->Hs) Ha = w->Hs;
    if (!w->primed) { w->anaPos = w->rpos; w->primed = 1; }

    int off = DSWsBestOffset(w, w->anaPos, w->prevTail, w->Hs);
    long start = w->anaPos + off;
    if (start < w->rpos) start = w->rpos;

    for (int i = 0; i < w->win; i++) {
        float tri = (i < w->Hs) ? (float)i / w->Hs : (float)(w->win - i) / w->Hs;
        w->accum[i] += DSWsAt(w, start + i) * tri;
    }
    for (int i = 0; i < w->Hs; i++) {
        float v = w->accum[i];
        if (v > 32767) v = 32767; if (v < -32768) v = -32768;
        outHs[i] = (int16_t)v;
    }
    for (int i = 0; i < w->Hs; i++) w->prevTail[i] = DSWsAt(w, start + w->Hs + i);
    memmove(w->accum, w->accum + w->Hs, (w->win - w->Hs) * sizeof(float));
    memset(w->accum + (w->win - w->Hs), 0, w->Hs * sizeof(float));
    w->anaPos = start + Ha;
    if (w->anaPos > w->wpos) w->anaPos = w->wpos;
}

#pragma mark - السرعة الحية: تأخير ثم لحاق (WSOLA لكل متكلم، النغمة محفوظة)
// الصوت المباشر لا يمكن تسريعه فوق سرعة وصوله. الحل: "تجميع" تأخير قصير بصمت ثم تشغيل المتجمّع مسرّعاً
// (x1.5..x4) بنغمة طبيعية حتى نلحق البث الحي، وبعدها يرجع تلقائياً 1x بلا تقطيع.
// المحرك يُختبر بمعزل عن اللعبة (انظر README) ولا يمسّ إلا صوت المتكلمين القادم لجهازك.
#define DSL_MAXHS 512
#define DSL_BURST 0.25f   // دفعة التشغيل المسرّع بعد التأخير (ثانية)
#define DSL_OUTQ  16384

typedef struct {
    int sr, Hs, N, D;
    int16_t *ring; long ringSize;
    long wpos; double rp; long last;
    int state;                    // 0 = تشغيل/لحاق، 1 = تجميع (صمت)
    long accumT, floorS;          // floorS = التأخير الدائم المختار، accumT = floorS + دفعة
    float accum[2 * DSL_MAXHS];
    int16_t outq[DSL_OUTQ]; int oHead, oCount;
    float lastSpeed;
    int seenRestart, seenLive;
} DSLiveEng;

static inline int16_t DSLAt(DSLiveEng *e, long pos) {
    long m = pos % e->ringSize; if (m < 0) m += e->ringSize;
    return e->ring[m];
}

static void DSLEngInit(DSLiveEng *e, int sr) {
    if (e->ring) free(e->ring);
    memset(e, 0, sizeof *e);
    e->sr = sr;
    e->Hs = sr / 100; if (e->Hs > DSL_MAXHS) e->Hs = DSL_MAXHS; if (e->Hs < 80) e->Hs = 80;
    e->N = 2 * e->Hs; e->D = e->Hs / 2;
    e->ringSize = (long)sr * 45;
    e->ring = (int16_t *)calloc((size_t)e->ringSize, sizeof(int16_t));
    e->last = -1; e->lastSpeed = 1.0f;
    e->seenRestart = gLiveRestartGen; e->seenLive = gLiveLiveGen;
}

static void DSLGoLive(DSLiveEng *e) {
    long keep = (long)e->N + e->D + 2L * e->Hs;
    long rp = e->wpos - keep; if (rp < 0) rp = 0;
    e->rp = (double)rp; e->last = -1; e->state = 0;
    e->oHead = 0; e->oCount = 0;
    memset(e->accum, 0, sizeof e->accum);
}

static long DSLNeedRing(int sr, int delaySec) {   // حجم البفر: التأخير + 30 ث (حدّ أدنى 45 ث)
    long sec = (long)delaySec + 30L; if (sec < 45L) sec = 45L;
    return (long)sr * sec;
}

static void DSLStartAccum(DSLiveEng *e, int delaySec) {
    (void)delaySec;   // التأخير المختار يُطبَّق كل نداء في DSLProcess (floorS / accumT)
    e->rp = (double)e->wpos; e->last = -1; e->state = 1;
}

static int DSLHop(DSLiveEng *e, float speed) {
    if (e->oCount + e->Hs > DSL_OUTQ) return 0;
    long behind = e->wpos - (long)e->rp;
    if (speed > 1.0f) {
        // وضع «متأخر دائماً»: يظل خلف البث بمقدار التأخير المختار ولا يرجع للبث الحي أبداً.
        // يشغّل مسرّعاً ما فوق التأخير، وإذا قرب منه يتوقف (صمت) حتى تتجمع دفعة جديدة.
        if (e->state == 1) { if (behind >= e->accumT) e->state = 0; else return 0; }
        else if (behind <= e->floorS + (long)(e->Hs * speed) + e->N + e->D) { e->state = 1; return 0; }
    } else if (e->state == 1) {
        if (behind >= e->accumT) e->state = 0; else return 0;
    }
    long backlog = behind - (e->N + e->D);
    if (backlog < 0) return 0;
    float eff = speed;
    long s = (long)e->rp;
    if (e->last >= 0 && s != e->last + e->Hs) {   // محاذاة WSOLA: أفضل إزاحة تتصل بسلاسة بالمقطع السابق
        long t = e->last + e->Hs, bs = s; double best = -1e30;
        for (long d = -e->D; d <= e->D; d += 2) {
            long c = s + d;
            if (c < 0 || c + e->N > e->wpos) continue;
            double sum = 0, en = 1e-9;
            for (int j = 0; j < e->Hs; j += 4) {
                double a = DSLAt(e, t + j), b = DSLAt(e, c + j);
                sum += a * b; en += b * b;
            }
            double score = sum / sqrt(en);
            if (score > best) { best = score; bs = c; }
        }
        s = bs;
    }
    for (int i = 0; i < e->N; i++) {
        float w = (i < e->Hs) ? (float)i / e->Hs : (float)(e->N - i) / e->Hs;
        e->accum[i] += DSLAt(e, s + i) * w;
    }
    for (int i = 0; i < e->Hs; i++) {
        float v = e->accum[i];
        if (v > 32767.f) v = 32767.f; if (v < -32768.f) v = -32768.f;
        e->outq[(e->oHead + e->oCount + i) % DSL_OUTQ] = (int16_t)v;
    }
    e->oCount += e->Hs;
    memmove(e->accum, e->accum + e->Hs, e->Hs * sizeof(float));
    memset(e->accum + e->Hs, 0, e->Hs * sizeof(float));
    e->last = s; e->rp += e->Hs * eff;
    return 1;
}

// يعالج n عيّنة mono في المكان (buf). يُستدعى من خيط صوت Agora.
static void DSLProcess(DSLiveEng *e, int16_t *buf, int n, float speed, int delaySec) {
    if (delaySec < 0) delaySec = 0; if (delaySec > 1800) delaySec = 1800;
    long needRing = DSLNeedRing(e->sr, delaySec);
    if (needRing != e->ringSize) {          // تغيّر التأخير: بفر بالحجم المناسب (calloc كسول، الذاكرة تُستهلك تدريجياً)
        int16_t *nr = (int16_t *)calloc((size_t)needRing, sizeof(int16_t));
        if (nr) {
            free(e->ring); e->ring = nr; e->ringSize = needRing;
            e->wpos = 0; e->rp = 0; e->last = -1; e->oHead = 0; e->oCount = 0; e->state = 0;
            memset(e->accum, 0, sizeof e->accum);
            if (speed > 1.0f) DSLStartAccum(e, delaySec);
        }
    }
    e->floorS = (long)delaySec * e->sr;
    long maxFloor = e->ringSize - 20L * e->sr; if (maxFloor < 0) maxFloor = 0;   // يترك 20 ث أمان قبل أن يدور البفر
    if (e->floorS > maxFloor) e->floorS = maxFloor;
    e->accumT = e->floorS + (long)(e->sr * DSL_BURST);
    if (e->seenLive != gLiveLiveGen) { e->seenLive = gLiveLiveGen; DSLGoLive(e); }
    if (e->seenRestart != gLiveRestartGen) {
        e->seenRestart = gLiveRestartGen;
        if (speed > 1.0f) DSLStartAccum(e, delaySec); else DSLGoLive(e);
    }
    if (speed != e->lastSpeed) {
        e->lastSpeed = speed;
        if (speed <= 1.0f) DSLGoLive(e);
        else if (e->state == 0 && (e->wpos - (long)e->rp - (e->N + e->D)) < e->sr) DSLStartAccum(e, delaySec);
        // لو يوجد تراكم أكثر من ثانية (نلحق الآن): نكمل بالسرعة الجديدة بدون إعادة تجميع
    }
    for (int i = 0; i < n; i++) e->ring[(e->wpos + i) % e->ringSize] = buf[i];
    e->wpos += n;
    if (e->wpos - (long)e->rp > e->ringSize - 4L * e->Hs) e->rp = (double)(e->wpos - e->ringSize / 2);
    for (int g = 0; g < 16 && e->oCount < n; g++) if (!DSLHop(e, speed)) break;
    int take = e->oCount < n ? e->oCount : n;
    for (int i = 0; i < take; i++) buf[i] = e->outq[(e->oHead + i) % DSL_OUTQ];
    for (int i = take; i < n; i++) buf[i] = 0;
    e->oHead = (e->oHead + take) % DSL_OUTQ; e->oCount -= take;

    if (e->state == 1) {                                   // حالة العرض في المنيو الصغير
        gLiveMode = 1;
        gLiveA = (int)((e->wpos - (long)e->rp) * 1000L / e->sr);
        gLiveB = (int)(e->accumT * 1000L / e->sr);
    } else {
        long bl = e->wpos - (long)e->rp - (e->N + e->D);
        if (speed > 1.0f && bl > 2L * e->Hs) { long ex = bl - e->floorS; if (ex < 0) ex = 0; gLiveMode = 2; gLiveA = (int)(ex * 1000L / e->sr); gLiveB = 0; }
        else { gLiveMode = 0; gLiveA = 0; gLiveB = 0; }
    }
}

static DSLiveEng *gLiveEngs[8];
static NSUInteger gLiveUids[8];
static int gLiveCount = 0, gLiveNext = 0;

static DSLiveEng *DSLEngForUid(NSUInteger uid, int sr) {
    if (sr < 8000 || sr > 48000) return NULL;
    int idx = -1;
    for (int i = 0; i < gLiveCount; i++) if (gLiveUids[i] == uid) { idx = i; break; }
    if (idx < 0) {
        if (gLiveCount < 8) idx = gLiveCount++;
        else { idx = gLiveNext; gLiveNext = (gLiveNext + 1) % 8; }
        if (!gLiveEngs[idx]) gLiveEngs[idx] = (DSLiveEng *)calloc(1, sizeof(DSLiveEng));
        if (!gLiveEngs[idx]) return NULL;
        gLiveUids[idx] = uid;
        DSLEngInit(gLiveEngs[idx], sr);
    }
    DSLiveEng *e = gLiveEngs[idx];
    if (e->sr != sr) DSLEngInit(e, sr);
    return e->ring ? e : NULL;
}

#pragma mark - تقوية الصوت (Output Gain) — مقوّي نهائي مع ليميتر ناعم يمنع التشويه
// معامل التقوية (1.0 = بدون). يُضرب مباشرة بعيّنات المخرج، ويمرّ بعدها على ليميتر ناعم (tanh) فوق 0.85
// حتى لا يتحول الرفع الزائد إلى تقطيع حاد (clipping). القيمة الخارجة دائماً أقل من 1.0.

static inline float DSSoftLimit(float x) {
    const float T = 0.85f;
    float a = fabsf(x);
    if (a <= T) return x;
    float o = T + (1.0f - T) * tanhf((a - T) / (1.0f - T));
    return x < 0 ? -o : o;
}
static void DSGainF32(float *p, size_t n, float g) {
    for (size_t i = 0; i < n; i++) p[i] = DSSoftLimit(p[i] * g);
}
static void DSGainI16(int16_t *p, size_t n, float g) {
    const float k = g / 32768.0f;
    for (size_t i = 0; i < n; i++) p[i] = (int16_t)lrintf(DSSoftLimit((float)p[i] * k) * 32767.0f);
}

#pragma mark - السرعة الحية لكل الصوت (RemoteIO): Zego وأي محرك صوت آخر
// يلتفّ حول دوال التشغيل (render callbacks) لوحدات AudioUnit بالتطبيق، فيمسك مخرج الصوت قبل السماعة
// مهما كان المحرك (Zego / FMOD / غيره). يُطبَّق نفس محرك التجميع ثم اللحاق. ملاحظة: يشمل كل ما يمرّ بتلك الوحدة
// (أصوات اللعبة أيضاً) لأنه يعمل على المخرج النهائي، لذلك هو خيار منفصل يُشغَّل يدوياً من المنيو الصغير.
#define DS_MAX_GLOBAL_ENGINES 6
static int gGlobEngineCount = 0;

typedef struct {
    AURenderCallback proc; void *refcon; AudioUnit unit;
    AudioStreamBasicDescription fmt; int haveFmt;
    DSLiveEng *eng;
    BOOL fromAgora;   // الدالة الأصلية تابعة لمكتبة Agora (تقوية Agora الرسمية تكفي، فلا نضاعفها)
    DSAPState *ap;    // AUDIO PRO: حالة معالجة هذه الوحدة (مرشحات/ضاغط/بوابة)
} DSRW;

// تقوية المخرج النهائي لوحدة صوت واحدة (Zego / FMOD / أي محرك). تعمل بالمكان على مخزن الصوت.
static void DSApplyOutputGain(DSRW *w, AudioUnitRenderActionFlags *flags, UInt32 bus, UInt32 frames, AudioBufferList *io) {
    if (flags && (*flags & kAudioUnitRenderAction_OutputIsSilence)) return;
    if (!w->haveFmt) {
        UInt32 sz = sizeof w->fmt;
        if (AudioUnitGetProperty(w->unit, kAudioUnitProperty_StreamFormat, kAudioUnitScope_Input, bus, &w->fmt, &sz) != noErr) return;
        w->haveFmt = 1;
    }
    const AudioStreamBasicDescription *f = &w->fmt;
    if (f->mFormatID != kAudioFormatLinearPCM) return;
    BOOL isFloat = (f->mFormatFlags & kAudioFormatFlagIsFloat) != 0;
    BOOL nonInter = (f->mFormatFlags & kAudioFormatFlagIsNonInterleaved) != 0;
    if (isFloat ? f->mBitsPerChannel != 32 : f->mBitsPerChannel != 16) return;
    size_t bps = isFloat ? 4 : 2;
    float g = gDSGain;
    for (UInt32 i = 0; i < io->mNumberBuffers; i++) {
        void *d = io->mBuffers[i].mData; if (!d) continue;
        size_t perFrame = nonInter ? 1 : (io->mBuffers[i].mNumberChannels ? io->mBuffers[i].mNumberChannels : 1);
        size_t cnt = io->mBuffers[i].mDataByteSize / bps, want = (size_t)frames * perFrame;
        if (cnt > want) cnt = want;
        if (isFloat) DSGainF32((float *)d, cnt, g); else DSGainI16((int16_t *)d, cnt, g);
    }
}

// AUDIO PRO: معالجة الصوت (بوابة ← قطع دندنة ← EQ ← ضاغط ← ليميتر) على مخرج الوحدة بالمكان. تعمل على كتل 256 إطار
// (مصفوفات صغيرة على المكدس) فلا تخصيص ذاكرة ولا مخزن مشترك بين الخيوط. بلا مخزن/تأخير: ~0ms.
static void DSApplyProcessing(DSRW *w, AudioUnitRenderActionFlags *flags, UInt32 bus, UInt32 frames, AudioBufferList *io) {
    if (!w->ap) return;
    if (flags && (*flags & kAudioUnitRenderAction_OutputIsSilence)) return;
    if (!w->haveFmt) {
        UInt32 sz = sizeof w->fmt;
        if (AudioUnitGetProperty(w->unit, kAudioUnitProperty_StreamFormat, kAudioUnitScope_Input, bus, &w->fmt, &sz) != noErr) return;
        w->haveFmt = 1;
    }
    const AudioStreamBasicDescription *f = &w->fmt;
    if (f->mFormatID != kAudioFormatLinearPCM) return;
    BOOL isFloat = (f->mFormatFlags & kAudioFormatFlagIsFloat) != 0;
    BOOL nonInter = (f->mFormatFlags & kAudioFormatFlagIsNonInterleaved) != 0;
    if (isFloat ? f->mBitsPerChannel != 32 : f->mBitsPerChannel != 16) return;
    int sr = (int)f->mSampleRate; if (sr < 8000 || sr > 96000) return;
    UInt32 nb = io->mNumberBuffers;
    int ch = nonInter ? (int)nb : (nb ? (int)io->mBuffers[0].mNumberChannels : 0);
    if (ch < 1 || ch > 2) return;
    UInt32 bps = isFloat ? 4 : 2;
    for (UInt32 i = 0; i < nb; i++) {
        UInt32 need = frames * bps * (nonInter ? 1 : (UInt32)ch);
        if (!io->mBuffers[i].mData || io->mBuffers[i].mDataByteSize < need) return;
    }
    DSAPState *s = w->ap;
    if (s->sr != sr) memset(s, 0, sizeof *s);
    if (s->sr != sr || s->gen != gAP.gen) DSAPUpdate(s, sr);

    void *pb[2] = { io->mBuffers[0].mData, (nonInter && nb > 1) ? io->mBuffers[1].mData : io->mBuffers[0].mData };
    const size_t stride = nonInter ? 1 : (size_t)ch;
    const size_t off1 = nonInter ? 0 : 1;   // موضع القناة اليمنى داخل الإطار
    float L[256], R[256];
    for (UInt32 base = 0; base < frames; base += 256) {
        int n = (int)((frames - base) < 256 ? (frames - base) : 256);
        for (int k = 0; k < n; k++) {
            size_t i0 = (base + k) * stride, i1 = i0 + off1;
            if (isFloat) { L[k] = ((float *)pb[0])[i0]; R[k] = ch > 1 ? ((float *)pb[1])[i1] : L[k]; }
            else { L[k] = ((int16_t *)pb[0])[i0] * (1.0f / 32768.0f); R[k] = ch > 1 ? ((int16_t *)pb[1])[i1] * (1.0f / 32768.0f) : L[k]; }
        }
        DSAPProcess(s, L, R, n, ch > 1);
        for (int k = 0; k < n; k++) {
            size_t i0 = (base + k) * stride, i1 = i0 + off1;
            if (isFloat) { ((float *)pb[0])[i0] = L[k]; if (ch > 1) ((float *)pb[1])[i1] = R[k]; }
            else {
                float a = L[k] * 32767.0f; if (a > 32767.f) a = 32767.f; if (a < -32768.f) a = -32768.f;
                ((int16_t *)pb[0])[i0] = (int16_t)lrintf(a);
                if (ch > 1) { float b = R[k] * 32767.0f; if (b > 32767.f) b = 32767.f; if (b < -32768.f) b = -32768.f; ((int16_t *)pb[1])[i1] = (int16_t)lrintf(b); }
            }
        }
    }
}

static OSStatus DSRenderWrap(void *ref, AudioUnitRenderActionFlags *flags, const AudioTimeStamp *ts,
                             UInt32 bus, UInt32 frames, AudioBufferList *io) {
    DSRW *w = (DSRW *)ref;
    OSStatus r = w->proc(w->refcon, flags, ts, bus, frames, io);
    if (r == noErr && gAP.on && w->ap && io && frames > 0 && frames <= 8192) DSApplyProcessing(w, flags, bus, frames, io);   // AUDIO PRO (قبل التقوية)
    if (r == noErr && gDSGain > 1.0f && io && frames > 0 && frames <= 8192 && !(w->fromAgora && gDSAgoraGainOK))
        DSApplyOutputGain(w, flags, bus, frames, io);   // تقوية الصوت (قبل معالجة السرعة الحية إن كانت مفعّلة)
    if (r != noErr || !gLiveSpeedOn || !gLiveGlobal || gLiveSpeed <= 1.0f || !io || frames == 0 || frames > 4096) return r;
    if (!w->haveFmt) {
        UInt32 sz = sizeof w->fmt;
        if (AudioUnitGetProperty(w->unit, kAudioUnitProperty_StreamFormat, kAudioUnitScope_Input, bus, &w->fmt, &sz) != noErr) return r;
        w->haveFmt = 1;
    }
    const AudioStreamBasicDescription *f = &w->fmt;
    if (f->mFormatID != kAudioFormatLinearPCM) return r;
    BOOL isFloat = (f->mFormatFlags & kAudioFormatFlagIsFloat) != 0;
    BOOL nonInter = (f->mFormatFlags & kAudioFormatFlagIsNonInterleaved) != 0;
    if (isFloat ? f->mBitsPerChannel != 32 : f->mBitsPerChannel != 16) return r;
    int sr = (int)f->mSampleRate; if (sr < 8000 || sr > 48000) return r;
    UInt32 nb = io->mNumberBuffers;
    int ch = nonInter ? (int)nb : (nb ? (int)io->mBuffers[0].mNumberChannels : 0);
    if (ch < 1 || ch > 2) return r;
    UInt32 bps = isFloat ? 4 : 2;
    for (UInt32 i = 0; i < nb; i++) {
        UInt32 need = frames * bps * (nonInter ? 1 : (UInt32)ch);
        if (!io->mBuffers[i].mData || io->mBuffers[i].mDataByteSize < need) return r;
    }
    if (!w->eng) {   // محرك مستقل لكل وحدة/مدخل، حتى لا تختلط مصادر مختلفة
        if (gGlobEngineCount >= DS_MAX_GLOBAL_ENGINES) return r;
        w->eng = (DSLiveEng *)calloc(1, sizeof(DSLiveEng));
        if (!w->eng) return r;
        gGlobEngineCount++;
    }
    if (!w->eng->ring || w->eng->sr != sr) DSLEngInit(w->eng, sr);
    if (!w->eng->ring) return r;

    static int16_t mono[4096];
    BOOL silent = flags && (*flags & kAudioUnitRenderAction_OutputIsSilence);
    for (UInt32 i = 0; i < frames; i++) {
        float acc = 0;
        if (!silent) {
            for (int c = 0; c < ch; c++) {
                if (isFloat) acc += (nonInter ? ((float *)io->mBuffers[c].mData)[i] : ((float *)io->mBuffers[0].mData)[i * ch + c]) * 32767.0f;
                else acc += nonInter ? ((int16_t *)io->mBuffers[c].mData)[i] : ((int16_t *)io->mBuffers[0].mData)[i * ch + c];
            }
            acc /= ch;
        }
        if (acc > 32767.f) acc = 32767.f; if (acc < -32768.f) acc = -32768.f;
        mono[i] = (int16_t)acc;
    }
    DSLProcess(w->eng, mono, (int)frames, gLiveSpeed, gLiveDelay);
    for (UInt32 i = 0; i < frames; i++) {
        for (int c = 0; c < ch; c++) {
            if (isFloat) { float v = mono[i] / 32768.0f; if (nonInter) ((float *)io->mBuffers[c].mData)[i] = v; else ((float *)io->mBuffers[0].mData)[i * ch + c] = v; }
            else { if (nonInter) ((int16_t *)io->mBuffers[c].mData)[i] = mono[i]; else ((int16_t *)io->mBuffers[0].mData)[i * ch + c] = mono[i]; }
        }
    }
    if (flags) *flags &= ~kAudioUnitRenderAction_OutputIsSilence;
    return r;
}

static OSStatus hook_AudioUnitSetProperty(AudioUnit unit, AudioUnitPropertyID pid, AudioUnitScope scope,
                                          AudioUnitElement el, const void *data, UInt32 size) {
    if (pid == kAudioUnitProperty_SetRenderCallback && scope == kAudioUnitScope_Input && data && size >= sizeof(AURenderCallbackStruct)) {
        const AURenderCallbackStruct *cs = (const AURenderCallbackStruct *)data;
        if (cs->inputProc && cs->inputProc != (AURenderCallback)DSRenderWrap) {
            DSRW *w = (DSRW *)calloc(1, sizeof(DSRW));
            if (w) {
                w->ap = (DSAPState *)calloc(1, sizeof(DSAPState));
                w->proc = cs->inputProc; w->refcon = cs->inputProcRefCon; w->unit = unit;
                Dl_info di; if (dladdr((const void *)cs->inputProc, &di) && di.dli_fname && strcasestr(di.dli_fname, "agora")) w->fromAgora = YES;
                AURenderCallbackStruct n = { (AURenderCallback)DSRenderWrap, w };
                return orig_AudioUnitSetProperty(unit, pid, scope, el, &n, sizeof n);
            }
        }
    }
    return orig_AudioUnitSetProperty(unit, pid, scope, el, data, size);
}

// ---- ربط Agora: مراقب صوت خام رسمي (AgoraAudioDataFrameProtocol) — يعالج الصوت القادم لجهازك فقط ----
static DSWsola gVoiceWs[8];              // قناة لكل "uid" متكلم، حتى ما تتداخل أصوات اللاعبين ببعض
static NSMapTable *gVoiceWsByUid;        // uid -> فهرس في gVoiceWs
static dispatch_once_t gVoiceWsOnce;

static DSWsola *DSWsForUid(NSUInteger uid) {
    dispatch_once(&gVoiceWsOnce, ^{
        gVoiceWsByUid = [NSMapTable strongToStrongObjectsMapTable];
        for (int i = 0; i < 8; i++) DSWsInit(&gVoiceWs[i], 48000);
    });
    NSNumber *key = @(uid);
    NSNumber *idx = [gVoiceWsByUid objectForKey:key];
    if (!idx) {
        static int next = 0;
        idx = @(next % 8); next++;
        [gVoiceWsByUid setObject:idx forKey:key];
        DSWsInit(&gVoiceWs[idx.intValue], 48000);
    }
    return &gVoiceWs[idx.intValue];
}

@protocol DSAgoraAudioDataFrameProtocol <NSObject>
@optional
- (BOOL)onRecordAudioFrame:(id)frame;
- (BOOL)onPlaybackAudioFrame:(id)frame;
- (BOOL)onMixedAudioFrame:(id)frame;
- (BOOL)onPlaybackAudioFrameBeforeMixing:(id)frame uid:(NSUInteger)uid;
- (BOOL)onPlaybackAudioFrameBeforeMixingEx:(id)frame channelId:(NSString *)channelId uid:(NSUInteger)uid;
- (BOOL)isMultipleChannelFrameWanted;
@end

@interface DSAudioFrameProxy : NSObject <DSAgoraAudioDataFrameProtocol>
@end
@implementation DSAudioFrameProxy
// نعالج الصوت *قبل الخلط* لكل متكلم على حدة (uid)، حتى التسريع ما يشوّش أصوات بعض ببعض
- (BOOL)onPlaybackAudioFrameBeforeMixing:(id)frameObj uid:(NSUInteger)uid {
    if (!gLiveSpeedOn && ![DSSettings shared].voiceSpeedOn) return YES;
    if (gLiveSpeedOn && gLiveGlobal) return YES;   // وضع «كل الصوت» يعالج المخرج النهائي بدل Agora
    @try {
        id bufVal = [frameObj valueForKey:@"buffer"];   // قد يصل كـ NSValue يغلّف مؤشر void* (وليس مؤشراً مباشراً)
        int16_t *buf = NULL;
        if ([bufVal isKindOfClass:[NSValue class]]) buf = (int16_t *)[(NSValue *)bufVal pointerValue];
        else if ([bufVal isKindOfClass:[NSNumber class]]) buf = (int16_t *)(uintptr_t)[(NSNumber *)bufVal unsignedLongLongValue];
        else buf = NULL;
        NSInteger samplesPerChannel = [[frameObj valueForKey:@"samplesPerChannel"] integerValue];
        NSInteger channels = [[frameObj valueForKey:@"channels"] integerValue];
        NSInteger sr = [[frameObj valueForKey:@"samplesPerSec"] integerValue];
        if (!buf || samplesPerChannel <= 0 || samplesPerChannel > 1024 || channels < 1 || channels > 2 || sr < 8000 || sr > 48000) return YES;
        if (gLiveSpeedOn) {   // السرعة الحية: تجميع ثم لحاق بنغمة طبيعية (حتى 4x)
            DSLiveEng *le = DSLEngForUid(uid, (int)sr);
            if (!le) return YES;
            float sp = gLiveSpeed; int dl = gLiveDelay;
            if (channels == 1) DSLProcess(le, buf, (int)samplesPerChannel, sp, dl);
            else {   // ستيريو: ندمج لأحادي ثم نكرر على القناتين
                static int16_t mono[1024];
                for (NSInteger i = 0; i < samplesPerChannel; i++) mono[i] = (int16_t)(((int)buf[i*2] + (int)buf[i*2+1]) / 2);
                DSLProcess(le, mono, (int)samplesPerChannel, sp, dl);
                for (NSInteger i = 0; i < samplesPerChannel; i++) { buf[i*2] = mono[i]; buf[i*2+1] = mono[i]; }
            }
            return YES;
        }
        DSWsola *w = DSWsForUid(uid);
        if (w->sr != (int)sr) DSWsInit(w, (int)sr);
        float maxSpeed = [DSSettings shared].voiceSpeedMax;

        if (channels == 1) {
            DSWsFeed(w, buf, (int)samplesPerChannel);
            int16_t out[1024];
            DSWsStep(w, out, maxSpeed);
            memcpy(buf, out, samplesPerChannel * sizeof(int16_t));
        } else {   // ستيريو: نفصل القناتين، نعالج كل وحدة بنفس قرار المحاذاة، ثم نعيد التشبيك
            static int16_t left[1024], right[1024], outL[1024], outR[1024];
            for (NSInteger i = 0; i < samplesPerChannel; i++) { left[i] = buf[i*2]; right[i] = buf[i*2+1]; }
            DSWsFeed(w, left, (int)samplesPerChannel);
            DSWsStep(w, outL, maxSpeed);
            DSWsFeed(w, right, (int)samplesPerChannel);   // ملاحظة: يعالج القناتين بتوقيت مستقل بسيط؛ كافٍ لصوت بشري أحادي المصدر عادة
            DSWsStep(w, outR, maxSpeed);
            for (NSInteger i = 0; i < samplesPerChannel; i++) { buf[i*2] = outL[i]; buf[i*2+1] = outR[i]; }
        }
    } @catch (__unused NSException *e) { return YES; }   // أي خلل غير متوقع: مرّر الصوت الأصلي بدون تعديل، أبداً لا نكسر الاتصال
    return YES;
}
// Agora 3.7.3 (متأكَّد من ثنائي AgoraRtcKit): الغرف متعددة القنوات (AgoraRtcChannel) لا تصل إلا عبر نسخة Ex
// وبشرط أن يردّ المراقب YES على isMultipleChannelFrameWanted. المفتاح = uid + القناة حتى لا تتداخل القنوات.
- (BOOL)isMultipleChannelFrameWanted { return YES; }
- (BOOL)onPlaybackAudioFrameBeforeMixingEx:(id)frameObj channelId:(NSString *)channelId uid:(NSUInteger)uid {
    NSUInteger key = uid ^ ((NSUInteger)channelId.hash << 20);
    return [self onPlaybackAudioFrameBeforeMixing:frameObj uid:key];
}
- (BOOL)onPlaybackAudioFrame:(id)frame { return YES; }   // نعتمد "قبل الخلط" لكل متكلم على حدة؛ هذا احتياطي فقط
- (BOOL)onRecordAudioFrame:(id)frame { return YES; }
- (BOOL)onMixedAudioFrame:(id)frame { return YES; }
@end

static DSAudioFrameProxy *gDSAudioProxy;
#pragma mark - تقليل تأخير الصوت (مخزن Agora + مخزن الجهاز) + ملف إعدادات حرة

// الهدف: أقل تأخير ممكن لصوت الروم. المفاتيح مأخوذة من AgoraRtcKit الفعلي بالـ IPA (أسماؤها فقط، مو موثقة):
//   rtc.min_playout_delay[_speaker] / rtc.max_playout_delay : حدود تأخير مخزن الشبكة (NetEQ)
//   che.audio.neteq.fast_accelerate / acceleration_percent  : يسرّع التشغيل داخل المخزن لما يتراكم صوت (يقلل التأخير)
//   rtc.audience_latency_level=2                            : أقل تأخير للمستمع (يعمل بقنوات البث الحي فقط)
// + AVAudioSession.preferredIOBufferDuration (API رسمي من آبل) لتصغير مخزن مكبر الجهاز.
// لا يمكن إلغاء تأخير الشبكة نفسه (سفر الصوت من المتكلم لجهازك)، فقط تأخير المخازن.
static __weak id gDSLastEngine;

static BOOL DSForceZegoOnlyIsOn(void) { return gForceZegoOnly; }
static NSString *DSForceZegoOnlyTitle(void) { return gForceZegoOnly ? @"فرض Zego فقط: ON (Agora ممنوع من الانضمام)" : @"فرض Zego فقط: OFF"; }
static void DSForceZegoOnlyCycle(void) {
    DSSettings *st = [DSSettings shared];
    st.forceZegoOnly = !st.forceZegoOnly; [st save];
    gForceZegoOnly = st.forceZegoOnly;
}

static NSInteger DSAgoraLowLat(void) {   // 0 = OFF، 1 = خفيف، 2 = قوي، 3 = أقصى، 4 = تجريبي، 5 = الكل (كل المفاتيح)
    NSInteger l = [NSUserDefaults.standardUserDefaults integerForKey:@"DSAgoraLowLat"];
    return (l < 0 || l > 5) ? 0 : l;
}
static BOOL DSAgoraLowLatIsOn(void) { return DSAgoraLowLat() > 0; }
// المستوى 5 «الكل»: كل مفاتيح Agora الموجودة بالمكتبة (ما عدا dump لأنه يكتب ملفات على الجهاز).
// القسم الأول: اتجاهها معروف من اسمها (أقل تأخير). القسم الثاني: «استكشافية» قيمها تخمين بلا توثيق.
static const char *kAgoraAllKeys[][2] = {
    // --- اتجاهها واضح ---
    {"rtc.min_playout_delay", "0"}, {"rtc.min_playout_delay_speaker", "0"}, {"rtc.max_playout_delay", "150"},
    {"rtc.audience_latency_level", "2"}, {"rtc.channel.audience_latency_level", "2"},
    {"rtc.audience_low_latency", "true"}, {"rtc.audience_ultra_low_latency", "true"},
    {"che.audio.follow_system_io_buffer_duration", "true"}, {"che.audio.extra_playout_latency", "0"},
    {"che.audio.lowlatencycapture", "true"},
    {"che.audio.neteq.fast_accelerate", "true"}, {"che.audio.neteq.acceleration_percent", "100"},
    {"che.audio.neteq.acceleration_percent_internal", "100"}, {"che.audio.neteq.deceleration_percent", "0"},
    {"che.audio.neteq.deceleration_percent_internal", "0"}, {"che.audio.neteq.force_stretch", "true"},
    {"che.audio.neteq.accelerate.opt.enable", "true"}, {"che.audio.neteq.accelerate.min_future_ms", "10"},
    {"che.audio.neteq.accelerate.upper_bound", "100"}, {"che.audio.neteq.burst_max_limit_jitter_ms", "150"},
    {"che.audio.neteq.delay_tune", "0"}, {"che.audio.neteq.pre_buffer", "0"}, {"che.audio.neteq.pre_buffer_max_delay", "0"},
    // --- استكشافية (قيم مخمّنة) ---
    {"che.audio.neteq.accelerate.window_size", "20"}, {"che.audio.neteq.accelerate.opt.energy_threshold", "100"},
    {"che.audio.neteq.target_level_improve", "true"}, {"che.audio.neteq.target_level_set_improve", "true"},
    {"che.audio.neteq.improve_targetlevel_strategy", "1"}, {"che.audio.neteq.max_packets", "50"},
    {"che.audio.neteq.max_number_packets", "50"}, {"che.audio.neteq.max_peak_detector", "8"},
    {"che.audio.neteq.multi_plc", "true"}, {"che.audio.neteq.opus_plc", "true"},
    {"che.audio.neteq.burst_audience_factor", "1"}, {"che.audio.neteq.burst_comb_window_second", "1"},
    {"che.audio.neteq.burst_control_window_ms", "1000"}, {"che.audio.neteq.burst_freezing_num_threshold", "3"},
    {"che.audio.neteq.burst_jitter_improve_strategy", "1"}, {"che.audio.neteq.burst_peak_num_threshold", "3"},
    {"che.audio.neteq.burst_peak_trend_increased_threshold", "3"}, {"che.audio.neteq.burst_platform_ms", "100"},
    {"che.audio.neteq.burst_trend_threshold", "3"}, {"che.audio.playoutBufferLength", "40"},
    {"che.audio.min.iobuffer.duration", "0.005"},
};
#define DS_ALLKEYS_N ((int)(sizeof(kAgoraAllKeys) / sizeof(kAgoraAllKeys[0])))

// مفاتيح Zego (التطبيق يستخدم ZegoLiveRoom بوضع الغرف الثاني): تُرسل بصيغة "key=value" عبر +[ZegoLiveRoomApi setConfig:]
// وتُقرأ عند تهيئة المحرك، فتحتاج إعادة فتح اللعبة. الأسماء من نصوص المكتبة، والقيم تخمين.
static const char *kZegoKeys[] = {
    "enable_play_ultra_low_latency=true", "enable_ultra_low_latency=true", "prefer_play_ultra_source=1",
    "audio_jitter_break_threshold_ms=100", "jitter_level_compensation=0",   // قوّيناها: كان 200 — شدّدناه لنصه ضمن نفس نطاقه المعروف
    "play_buffer_level_ms_for_cdn_stream=0", "play_buffer_max_cache_interval_ms=100",   // قوّيناها: كان 200
};
#define DS_ZEGO_N ((int)(sizeof(kZegoKeys) / sizeof(kZegoKeys[0])))

static void DSZegoApplyConfig(void) {
    Class c = NSClassFromString(@"ZegoLiveRoomApi");
    SEL sel = NSSelectorFromString(@"setConfig:");
    if (!c || ![c respondsToSelector:sel]) return;
    for (int i = 0; i < DS_ZEGO_N; i++) {
        @try { ((void (*)(id, SEL, NSString *))objc_msgSend)((id)c, sel, [NSString stringWithUTF8String:kZegoKeys[i]]); } @catch (__unused NSException *e) {}
        NSLog(@"[AflatoonSuite] Zego setConfig %s", kZegoKeys[i]);
    }
}

static NSString *DSAgoraLowLatTitle(void) {
    NSInteger l = DSAgoraLowLat();
    if (l == 5) return [NSString stringWithFormat:@"تقليل تأخير الصوت: الكل (%d مفتاح)", DS_ALLKEYS_N + DS_ZEGO_N];
    NSArray *names = @[@"OFF", @"خفيف", @"قوي", @"أقصى", @"تجريبي"];
    return [NSString stringWithFormat:@"تقليل تأخير الصوت: %@", names[l]];
}

static void DSAgoraSetParameters(id engine, NSString *json) {
    if (!engine || !json.length) return;
    @try {
        SEL sel = NSSelectorFromString(@"setParameters:");
        if (![engine respondsToSelector:sel]) return;
        int r = ((int (*)(id, SEL, NSString *))objc_msgSend)(engine, sel, json);
        gDSKeyAll++; if (r == 0) gDSKeyOK++;
        NSLog(@"[AflatoonSuite] setParameters %@ -> %d", json, r);
    } @catch (__unused NSException *e) {}
}

static void DSAgoraApplyIOBuffer(double d) {
    dispatch_async(dispatch_get_main_queue(), ^{
        NSError *err = nil;
        [[AVAudioSession sharedInstance] setPreferredIOBufferDuration:d error:&err];
        NSLog(@"[AflatoonSuite] IO buffer %.4f s -> %@", d, err ? err.localizedDescription : @"ok");
    });
}

// تقوية 2: rtc.audience_latency_level=2 ليس تخميناً — هو القيمة الرسمية الموثقة AgoraAudienceLatencyLevelUltraLowLatency
// بتعداد Agora العام AgoraAudienceLatencyLevelType (AgoraEnumerates.h)، فنرسلها من المستوى 1 مباشرة بدل انتظار المستوى 2.
// rtc.audio.max_target_delay مفتاح رسمي موثّق باسمه الكامل بملف IAgoraParameter.h الرسمي من Agora (وليس تخميناً من نصوص الثنائي).
static void DSAgoraApplyLowLatency(id engine, NSInteger lvl) {
    if (lvl <= 0) return;
    if (lvl >= 5) {   // الكل: كل المفاتيح بالجدول + مخزن الجهاز 5ms
        for (int i = 0; i < DS_ALLKEYS_N; i++)
            DSAgoraSetParameters(engine, [NSString stringWithFormat:@"{\"%s\":%s}", kAgoraAllKeys[i][0], kAgoraAllKeys[i][1]]);
        DSAgoraSetParameters(engine, @"{\"rtc.audio.max_target_delay\":0}");
        DSAgoraApplyIOBuffer(0.005);
        dispatch_after(dispatch_time(DISPATCH_TIME_NOW, 3 * NSEC_PER_SEC), dispatch_get_main_queue(), ^{ DSAgoraApplyIOBuffer(0.005); });
        return;
    }
    int accel = (lvl == 1) ? 80 : 100;   // قوّيناها: كانت تبدأ بـ50% بالمستوى 1، صارت 80% من أول مستوى
    DSAgoraSetParameters(engine, @"{\"rtc.min_playout_delay\":0}");
    DSAgoraSetParameters(engine, @"{\"rtc.min_playout_delay_speaker\":0}");
    DSAgoraSetParameters(engine, @"{\"che.audio.neteq.fast_accelerate\":true}");
    DSAgoraSetParameters(engine, [NSString stringWithFormat:@"{\"che.audio.neteq.acceleration_percent\":%d}", accel]);
    DSAgoraSetParameters(engine, @"{\"rtc.audience_latency_level\":2}");            // رسمي موثق — من المستوى 1
    DSAgoraSetParameters(engine, @"{\"rtc.channel.audience_latency_level\":2}");
    if (lvl >= 2) {   // قوّيناها: هذي المفاتيح كانت تنتظر المستوى 4، صارت من المستوى 2
        DSAgoraSetParameters(engine, @"{\"che.audio.neteq.deceleration_percent\":0}");        // لا تبطّئ التشغيل (البطء = تأخير)
        DSAgoraSetParameters(engine, @"{\"che.audio.neteq.force_stretch\":true}");            // يجبر الضغط الزمني (تسريع) داخل المخزن
        DSAgoraSetParameters(engine, @"{\"che.audio.neteq.accelerate.opt.enable\":true}");    // تسريع محسّن
        DSAgoraSetParameters(engine, @"{\"che.audio.lowlatencycapture\":true}");              // التقاط منخفض التأخير (جهة الإرسال)
        DSAgoraSetParameters(engine, @"{\"rtc.audience_low_latency\":true}");
        DSAgoraSetParameters(engine, @"{\"che.audio.follow_system_io_buffer_duration\":true}");
        DSAgoraSetParameters(engine, [NSString stringWithFormat:@"{\"rtc.max_playout_delay\":%d}", lvl == 2 ? 150 : 100]);   // قوّيناها: كانت 300/150
        double d = (lvl == 2) ? 0.005 : 0.005;   // قوّيناها: مخزن IO صار 5ms من المستوى 2 (كان 10ms)
        DSAgoraApplyIOBuffer(d);
        dispatch_after(dispatch_time(DISPATCH_TIME_NOW, 3 * NSEC_PER_SEC), dispatch_get_main_queue(), ^{ DSAgoraApplyIOBuffer(d); });
    }
    if (lvl >= 4) {   // تجريبي: أقصى عدوانية (قيم إضافية مخمّنة من أسمائها، غير موثقة)
        DSAgoraSetParameters(engine, @"{\"che.audio.neteq.burst_max_limit_jitter_ms\":80}");  // قوّيناها: كان 150
        DSAgoraSetParameters(engine, @"{\"che.audio.extra_playout_latency\":0}");             // بدون تأخير إضافي للتشغيل
        DSAgoraSetParameters(engine, @"{\"rtc.audience_ultra_low_latency\":true}");
        DSAgoraSetParameters(engine, @"{\"rtc.audio.max_target_delay\":0}");                  // مفتاح رسمي موثّق — أقصى تأخير مستهدف = صفر
    }
}

#pragma mark - إعدادات الكيبورد الجديدة + Agora المتقدم (تُحفظ بـ NSUserDefaults)
static NSInteger DSKbNumMode(void) {
    NSInteger i = [NSUserDefaults.standardUserDefaults integerForKey:@"DSKbNum"];
    return (i < 0 || i > 3) ? 0 : i;
}
static BOOL DSKbNumIsOn(void) { return DSKbNumMode() > 0; }
static NSString *DSKbNumTitle(void) {
    NSArray *n = @[@"OFF", @"ترتيب", @"تدبيل", @"تدبيل الأخير"];
    return [NSString stringWithFormat:@"أرقام: %@", n[DSKbNumMode()]];
}
static void DSKbNumCycle(void) {
    NSInteger nx = (DSKbNumMode() + 1) % 4;
    [NSUserDefaults.standardUserDefaults setInteger:nx forKey:@"DSKbNum"];
    gKbNum = (int)nx;
}
static BOOL DSKbRevIsOn(void) { return [NSUserDefaults.standardUserDefaults boolForKey:@"DSKbRev"]; }
static NSString *DSKbRevTitle(void) { return DSKbRevIsOn() ? @"عكس الرسالة: ON" : @"عكس الرسالة: OFF"; }
static void DSKbRevToggle(void) {
    BOOL on = !DSKbRevIsOn();
    [NSUserDefaults.standardUserDefaults setBool:on forKey:@"DSKbRev"];
    gKbRev = on;
}
static BOOL DSKbNamesIsOn(void) { return [NSUserDefaults.standardUserDefaults boolForKey:@"DSKbNames"]; }
static NSString *DSKbNamesTitle(void) { return DSKbNamesIsOn() ? @"أسماء بحرف: ON" : @"أسماء بحرف: OFF"; }
static void DSKbNamesToggle(void) {
    BOOL on = !DSKbNamesIsOn();
    [NSUserDefaults.standardUserDefaults setBool:on forKey:@"DSKbNames"];
    gKbNames = on;
}
static NSInteger DSKbCatsMask(void) {
    id v = [NSUserDefaults.standardUserDefaults objectForKey:@"DSKbCats"];
    return v ? ([v integerValue] & 63) : 63;
}
static NSString *DSKbCatName(int bit) {
    NSArray *n = @[@"اسم ولد", @"اسم بنت", @"اسم حيوان", @"اسم نبات", @"اسم جماد", @"اسم دولة"];
    return (bit >= 0 && bit < 6) ? n[bit] : @"";
}
static void DSKbCatsToggleBit(int bit) {
    NSInteger m = DSKbCatsMask() ^ (1 << bit);
    [NSUserDefaults.standardUserDefaults setInteger:m forKey:@"DSKbCats"];
    gKbCats = (int)m;
}
static void DSKbXLoad(void) {
    gKbNum = (int)DSKbNumMode(); gKbRev = DSKbRevIsOn(); gKbNames = DSKbNamesIsOn(); gKbCats = (int)DSKbCatsMask();
    gKbKeep = [NSUserDefaults.standardUserDefaults boolForKey:@"DSKbKeep"];
}

// Agora المتقدم: مفاتيح Agora التي ضبطتها النسخة المعدّلة (لا نعرف أن كل مفتاح يؤثر على iOS؛ Agora يتجاهل غير المعروف بدون ضرر)
static NSInteger DSAgoraAdvMode(void) {
    NSInteger i = [NSUserDefaults.standardUserDefaults integerForKey:@"DSAgoraAdv"];
    return (i < 0 || i > 2) ? 0 : i;
}
static BOOL DSAgoraAdvIsOn(void) { return DSAgoraAdvMode() > 0; }
static NSString *DSAgoraAdvTitle(void) {
    NSArray *n = @[@"OFF", @"زمن أقل", @"زمن أقل + بدون معالجة"];
    return [NSString stringWithFormat:@"Agora متقدم: %@", n[DSAgoraAdvMode()]];
}
static void DSAudioApplyAgoraAdv(id engine) {
    NSInteger m = DSAgoraAdvMode();
    if (!engine || m <= 0) return;
    static const char *lat[][2] = {
        {"che.audio.neteq.max_packets", "2"}, {"che.audio.neteq.enable_fast_accelerate", "true"},
        {"che.audio.playout_delay_ms.min", "0"}, {"che.audio.playout_delay_ms.max", "0"},
        {"che.audio.playout.buffer.min", "0"}, {"che.audio.playout.buffer.max", "0"},
        {"che.audio.keep.audiosession", "true"}, {"che.audio.lowlatency", "true"}, {"rtc.audio.adm_enable_lowlatency", "true"} };
    static const char *raw[][2] = {
        {"che.audio.enable.aec", "false"}, {"che.audio.aec.enable", "false"},
        {"che.audio.enable.agc", "false"}, {"che.audio.agc.enable", "false"},
        {"che.audio.enable.ns", "false"}, {"che.audio.ns.enable", "false"}, {"che.audio.enable.nsng", "false"},
        {"che.audio.enable.howling_detect", "false"}, {"rtc.audio.howling_detect_enable", "false"}, {"rtc.audio.apm_enable", "0"} };
    for (size_t i = 0; i < sizeof lat / sizeof lat[0]; i++)
        DSAgoraSetParameters(engine, [NSString stringWithFormat:@"{\"%s\":%s}", lat[i][0], lat[i][1]]);
    if (m >= 2)
        for (size_t i = 0; i < sizeof raw / sizeof raw[0]; i++)
            DSAgoraSetParameters(engine, [NSString stringWithFormat:@"{\"%s\":%s}", raw[i][0], raw[i][1]]);
}
static void DSAgoraAdvCycle(void) {
    NSInteger nx = (DSAgoraAdvMode() + 1) % 3;
    [NSUserDefaults.standardUserDefaults setInteger:nx forKey:@"DSAgoraAdv"];
    DSAudioApplyAgoraAdv(gDSLastEngine);
}

#pragma mark - Ultra: ملف صوت متكامل + تكيّف تلقائي + تسريع العملية
// الأوضاع: 0 OFF · 1 متوازن (مخزن 40ms) · 2 سريع (0–120ms) · 3 أقصى (0–60ms + تسريع كامل).
// «تكيّف تلقائي»: يقيس PING كل 6 ثوانٍ وينزّل الوضع الفعّال فوراً إذا النت ضعيف (يمنع القطع)، ويرجّعه بعد 20 ثانية ثبات.
static volatile int gUltraEff = 0;                    // الوضع الفعّال الآن (بعد التكيّف)
static double gUltraRtt[6]; static int gUltraRttN = 0;   // آخر قياسات PING بالـ ms (سالب = فشل)
static double gUltraLastSwitch = 0;
static id gDSActivity;                                // توكن NSProcessInfo activity

static NSInteger DSUltraMode(void) {
    NSInteger i = [NSUserDefaults.standardUserDefaults integerForKey:@"DSUltraMode"];
    return (i < 0 || i > 3) ? 0 : i;
}
static BOOL DSUltraIsOn(void) { return DSUltraMode() > 0; }
static BOOL DSUltraAdaptive(void) { return [NSUserDefaults.standardUserDefaults boolForKey:@"DSUltraAdaptive"]; }
static BOOL DSUltraBoostOn(void) { return [NSUserDefaults.standardUserDefaults boolForKey:@"DSUltraBoost"]; }
static NSString *DSUltraModeName(NSInteger m) {
    NSArray *n = @[@"OFF", @"متوازن", @"سريع", @"أقصى"];
    return n[(m < 0 || m > 3) ? 0 : m];
}
static NSString *DSUltraTitle(void) {
    NSInteger m = DSUltraMode();
    NSString *t = [NSString stringWithFormat:@"Ultra: %@", DSUltraModeName(m)];
    if (m > 0 && DSUltraAdaptive() && gUltraEff != m) t = [t stringByAppendingFormat:@" (الآن: %@)", DSUltraModeName(gUltraEff)];
    return t;
}

// قرار التكيّف (دالة صرفة): الوضع الفعّال من وضع المستخدم وآخر قياسات RTT
static int DSUltraDecide(int user, const double *rtt, int n) {
    if (user <= 0) return 0;
    if (n < 3) return user;                      // لا بيانات كافية بعد
    double sum = 0, cnt = 0; int lost = 0;
    for (int i = 0; i < n; i++) { if (rtt[i] < 0) lost++; else { sum += rtt[i]; cnt++; } }
    if (cnt == 0) return 1;                      // كل القياسات فشلت: أأمن وضع
    double avg = sum / cnt, var = 0;
    for (int i = 0; i < n; i++) if (rtt[i] >= 0) var += (rtt[i] - avg) * (rtt[i] - avg);
    double jit = sqrt(var / cnt);
    int cap = 3;
    if (lost >= 2 || avg >= 150 || jit >= 45) cap = 1;
    else if (lost >= 1 || avg >= 90 || jit >= 25) cap = 2;
    return user < cap ? user : cap;
}

static void DSUltraApplyAgora(id engine) {
    int m = gUltraEff;
    if (!engine || m <= 0 || m > 3) return;
    static const int minD[4] = { 0, 40, 0, 0 }, maxD[4] = { 0, 250, 120, 60 }, acc[4] = { 0, 60, 80, 100 };
    DSAgoraSetParameters(engine, [NSString stringWithFormat:@"{\"rtc.min_playout_delay\":%d}", minD[m]]);
    DSAgoraSetParameters(engine, [NSString stringWithFormat:@"{\"rtc.min_playout_delay_speaker\":%d}", minD[m]]);
    DSAgoraSetParameters(engine, [NSString stringWithFormat:@"{\"rtc.max_playout_delay\":%d}", maxD[m]]);
    DSAgoraSetParameters(engine, [NSString stringWithFormat:@"{\"che.audio.neteq.acceleration_percent\":%d}", acc[m]]);
    DSAgoraSetParameters(engine, m >= 2 ? @"{\"che.audio.neteq.fast_accelerate\":true}" : @"{\"che.audio.neteq.fast_accelerate\":false}");
    if (m >= 3) {
        DSAgoraSetParameters(engine, @"{\"che.audio.neteq.force_stretch\":true}");
        DSAgoraSetParameters(engine, @"{\"rtc.audience_latency_level\":2}");
    }
}
static void DSUltraApplyBuffer(void) {
    int m = gUltraEff;
    if (m <= 0 || m > 3) return;
    double d = (m == 1) ? 0.010 : (m == 2 ? 0.005 : 0.0025);   // النظام يقرّب لأقرب قيمة يدعمها الجهاز
    dispatch_async(dispatch_get_main_queue(), ^{
        AVAudioSession *as = [AVAudioSession sharedInstance];
        [as setPreferredIOBufferDuration:d error:nil];
        if (m >= 2) [as setPreferredSampleRate:48000 error:nil];   // نفس تردد العتاد: بدون إعادة أخذ عينات (resampling)
    });
}
static void DSUltraSetEff(int m) {
    gUltraEff = m;
    DSUltraApplyAgora(gDSLastEngine);
    DSUltraApplyBuffer();
    if (m > 0) { if (gQoSMode < 1) gQoSMode = 1; }
    else gQoSMode = (int)DSAudioQoSMode();
}
// تسريع العملية: يطلب من النظام معاملة التطبيق كنشاط حساس للتأخير (تقليل تجميع المؤقّتات). أثره على iOS محدود وبسيط.
static void DSUltraBoostApply(BOOL on) {
    if (on && !gDSActivity)
        gDSActivity = [NSProcessInfo.processInfo beginActivityWithOptions:(NSActivityUserInitiatedAllowingIdleSystemSleep | NSActivityLatencyCritical)
                                                                   reason:@"AflatoonSuite Ultra audio"];
    else if (!on && gDSActivity) { [NSProcessInfo.processInfo endActivity:gDSActivity]; gDSActivity = nil; }
}
static void DSUltraReload(void) {
    gUltraRttN = 0; gUltraLastSwitch = 0;
    DSUltraSetEff((int)DSUltraMode());
    DSUltraBoostApply(DSUltraBoostOn());
}
static void DSUltraModeCycle(void) {
    NSInteger nx = (DSUltraMode() + 1) % 4;
    [NSUserDefaults.standardUserDefaults setInteger:nx forKey:@"DSUltraMode"];
    DSUltraReload();
}

static void DSUltraTick(void) {
    if (!DSUltraIsOn() || !DSUltraAdaptive()) return;
    uint32_t ip = 0; uint16_t pt = 0; NSString *nm = @"";
    DSPingResolveTarget(2, &ip, &pt, &nm);   // سيرفر اللعبة إن عُرف، وإلا Cloudflare
    if (!ip) return;
    dispatch_async(dispatch_get_global_queue(QOS_CLASS_UTILITY, 0), ^{
        double ms = DSPingProbe(ip, pt, 2.0);
        dispatch_async(dispatch_get_main_queue(), ^{
            if (gUltraRttN < 6) gUltraRtt[gUltraRttN++] = ms;
            else { memmove(gUltraRtt, gUltraRtt + 1, 5 * sizeof(double)); gUltraRtt[5] = ms; }
            int want = DSUltraDecide((int)DSUltraMode(), gUltraRtt, gUltraRttN);
            double now = CACurrentMediaTime();
            if (want < gUltraEff || (want > gUltraEff && now - gUltraLastSwitch > 20.0)) {   // نزول فوري، صعود بعد ثبات
                gUltraLastSwitch = now;
                DSUltraSetEff(want);
            }
        });
    });
}
static dispatch_source_t gUltraTimer;
static void DSUltraBoot(void) {
    DSUltraReload();
    if (gUltraTimer) return;
    gUltraTimer = dispatch_source_create(DISPATCH_SOURCE_TYPE_TIMER, 0, 0, dispatch_get_main_queue());
    dispatch_source_set_timer(gUltraTimer, dispatch_time(DISPATCH_TIME_NOW, 6 * NSEC_PER_SEC), 6 * NSEC_PER_SEC, 500 * NSEC_PER_MSEC);
    dispatch_source_set_event_handler(gUltraTimer, ^{ DSUltraTick(); });
    dispatch_resume(gUltraTimer);
}

#pragma mark - خيارات الصوت الجديدة: تقوية الصوت · أولوية الشبكة · مخزن الجهاز
// تُحفظ بـ NSUserDefaults (مثل تقليل التأخير): DSAudioGain (0..4) · DSAudioQoS (0..2) · DSAudioBuf (0..2)
static NSInteger DSAudioGainIdx(void) {
    NSInteger i = [NSUserDefaults.standardUserDefaults integerForKey:@"DSAudioGain"];
    return (i < 0 || i > 4) ? 0 : i;
}
static float DSAudioGainFactor(NSInteger i) { static const float f[5] = { 1.0f, 1.5f, 2.0f, 3.0f, 4.0f }; return f[(i < 0 || i > 4) ? 0 : i]; }
static BOOL DSAudioGainIsOn(void) { return DSAudioGainIdx() > 0; }
static NSString *DSAudioGainTitle(void) {
    NSInteger i = DSAudioGainIdx();
    return i ? [NSString stringWithFormat:@"تقوية الصوت: x%g", DSAudioGainFactor(i)] : @"تقوية الصوت: OFF";
}

// Agora: API رسمي adjustPlaybackSignalVolume (100 = الأصل، الحد الأعلى 400) — يقوّي كل ما يسمعه جهازك من الروم
static void DSAudioApplyAgoraGain(id engine) {
    if (!engine) return;
    SEL sel = NSSelectorFromString(@"adjustPlaybackSignalVolume:");
    if (![engine respondsToSelector:sel]) return;
    if (gDSGain <= 1.0f) {
        gDSAgoraGainOK = NO;
        if (gDSAgoraGainTouched) {   // رجوع للأصل بعد ما كانت التقوية مفعّلة
            @try { ((int (*)(id, SEL, NSInteger))objc_msgSend)(engine, sel, (NSInteger)100); } @catch (__unused NSException *e) {}
            gDSAgoraGainTouched = NO;
        }
        return;
    }
    @try {
        int r = ((int (*)(id, SEL, NSInteger))objc_msgSend)(engine, sel, (NSInteger)lroundf(gDSGain * 100.0f));
        gDSAgoraGainOK = (r == 0); gDSAgoraGainTouched = YES;
        NSLog(@"[AflatoonSuite] Agora playback gain %d%% -> %d", (int)lroundf(gDSGain * 100.0f), r);
    } @catch (__unused NSException *e) {}
}

static NSInteger DSAudioBufMode(void) {
    NSInteger i = [NSUserDefaults.standardUserDefaults integerForKey:@"DSAudioBuf"];
    return (i < 0 || i > 2) ? 0 : i;
}
static BOOL DSAudioBufIsOn(void) { return DSAudioBufMode() > 0; }
static NSString *DSAudioBufTitle(void) {
    NSArray *n = @[@"OFF", @"5ms", @"2.5ms"];
    return [NSString stringWithFormat:@"مخزن الجهاز: %@", n[DSAudioBufMode()]];
}
// النظام يقرّب الطلب لأقرب قيمة يدعمها الجهاز (غالباً 2.7 – 5.3ms). نعيد الطلب بعد ثوانٍ لأن اللعبة قد تعيد ضبط الجلسة.
static void DSAudioApplyBufferNow(void) {
    if (gUltraEff > 0) { DSUltraApplyBuffer(); return; }   // Ultra يتحكم بالمخزن حين يكون مفعّلاً
    NSInteger m = DSAudioBufMode(); if (m <= 0) return;
    double d = (m == 1) ? 0.005 : 0.0025;
    dispatch_async(dispatch_get_main_queue(), ^{
        NSError *err = nil;
        [[AVAudioSession sharedInstance] setPreferredIOBufferDuration:d error:&err];
        NSLog(@"[AflatoonSuite] device IO buffer %.4f s -> %@ (actual %.4f)", d, err ? err.localizedDescription : @"ok", AVAudioSession.sharedInstance.IOBufferDuration);
    });
}
static void DSAudioApplyBuffer(void) {
    if (!DSAudioBufIsOn()) return;
    DSAudioApplyBufferNow();
    for (NSNumber *s in @[@3.5, @8]) dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(s.doubleValue * NSEC_PER_SEC)), dispatch_get_main_queue(), ^{ DSAudioApplyBufferNow(); });
}

static NSInteger DSAudioQoSMode(void) {   // قيمة قديمة BOOL (YES) تُقرأ 1 = «الصوت»
    NSInteger i = [NSUserDefaults.standardUserDefaults integerForKey:@"DSAudioQoS"];
    return (i < 0 || i > 2) ? 0 : i;
}
static BOOL DSAudioQoSIsOn(void) { return DSAudioQoSMode() > 0; }
static NSString *DSAudioQoSTitle(void) {
    NSArray *n = @[@"OFF", @"الصوت", @"كل اللعبة"];
    return [NSString stringWithFormat:@"أولوية QoS: %@", n[DSAudioQoSMode()]];
}
static void DSAudioQoSToggle(void) {   // يدور: OFF ← الصوت ← كل اللعبة
    NSInteger next = (DSAudioQoSMode() + 1) % 3;
    [NSUserDefaults.standardUserDefaults setInteger:next forKey:@"DSAudioQoS"];
    gQoSMode = (int)next;
    if (gUltraEff > 0 && gQoSMode < 1) gQoSMode = 1;   // Ultra يحتاج وسم الصوت على الأقل
    memset(gQoSSeen, 0, sizeof gQoSSeen);   // الاتصالات الجديدة تتوسم؛ الجارية تتوسم عند أول connect/sendto لها
}

static void DSAudioGainCycle(void) {
    NSInteger next = (DSAudioGainIdx() + 1) % 5;
    [NSUserDefaults.standardUserDefaults setInteger:next forKey:@"DSAudioGain"];
    gDSGain = DSAudioGainFactor(next);
    DSAudioApplyAgoraGain(gDSLastEngine);   // لو ما في محرك بعد، يُطبَّق أول ما ينشأ
}
static void DSAudioBufCycle(void) {
    NSInteger next = (DSAudioBufMode() + 1) % 3;
    [NSUserDefaults.standardUserDefaults setInteger:next forKey:@"DSAudioBuf"];
    DSAudioApplyBuffer();
}

// عند الإقلاع: يحمّل الحالة المحفوظة، ويعيد طلب المخزن عند تغيّر المسار (سماعة/بلوتوث) أو انتهاء مقاطعة
static void DSAudioBoot(void) {
    DSKbXLoad();   // أوضاع الكيبورد الجديدة
    gDSGain = DSAudioGainFactor(DSAudioGainIdx());
    gQoSMode = (int)DSAudioQoSMode();
    DSAudioApplyBuffer();
    void (^again)(NSNotification *) = ^(NSNotification *n) {
        if ([n.name isEqualToString:AVAudioSessionInterruptionNotification]) {
            NSNumber *t = n.userInfo[AVAudioSessionInterruptionTypeKey];
            if (t.unsignedIntegerValue != AVAudioSessionInterruptionTypeEnded) return;
        }
        dispatch_after(dispatch_time(DISPATCH_TIME_NOW, 500 * NSEC_PER_MSEC), dispatch_get_main_queue(), ^{ DSAudioApplyBufferNow(); });
    };
    [[NSNotificationCenter defaultCenter] addObserverForName:AVAudioSessionRouteChangeNotification object:nil queue:nil usingBlock:again];
    [[NSNotificationCenter defaultCenter] addObserverForName:AVAudioSessionInterruptionNotification object:nil queue:nil usingBlock:again];
    DSAPBoot();      // AUDIO PRO: معالجة الصوت المحفوظة + مطابقة 48kHz
    DSUltraBoot();   // Ultra: الوضع المحفوظ + مؤقّت التكيّف + تسريع العملية
    DSSyncBoot();    // مزامنة الخادم الإداري (إن كانت مفعّلة)
}

#pragma mark - مزامنة الخادم الإداري (سياسة موقّعة)
// GET {base}/api/v1/policy?device=<id>&build=<ver>  ←  JSON + ترويسة X-Signature = hex(HMAC-SHA256(key, الجسم الخام))
// الجسم: {"gen":5,"devices":["*"],"set":{"DSAudioGain":2,"DSUltraMode":3},"message":"نص اختياري"}
// الأمان: https فقط · التوقيع إلزامي · gen لازم يزيد (يمنع إعادة سياسة قديمة) · مفاتيح مسموحة فقط وبحدود · المفتاح السري يبقى على جهازك.
// السياسة تغيّر الإعدادات المسموحة فقط؛ لا تحجب الأداة ولا توقفها. الخادم يستلم معرّف الجهاز العشوائي ورقم الإصدار فقط.
static NSString *DSDeviceId(void) {
    NSUserDefaults *d = NSUserDefaults.standardUserDefaults;
    NSString *i = [d stringForKey:@"DSDeviceId"];
    if (!i.length) { i = NSUUID.UUID.UUIDString; [d setObject:i forKey:@"DSDeviceId"]; }
    return i;
}
static BOOL DSSyncIsOn(void) { return [NSUserDefaults.standardUserDefaults boolForKey:@"DSSyncOn"]; }
static NSString *DSSyncURL(void) { return [NSUserDefaults.standardUserDefaults stringForKey:@"DSSyncURL"] ?: @""; }
static NSString *DSSyncKeyStr(void) { return [NSUserDefaults.standardUserDefaults stringForKey:@"DSSyncKey"] ?: @""; }
static NSString *DSSyncStatus(void) { return [NSUserDefaults.standardUserDefaults stringForKey:@"DSSyncLast"] ?: @"لم تتم مزامنة بعد"; }

static NSString *DSSyncHex(const uint8_t *b, size_t n) {
    NSMutableString *h = [NSMutableString stringWithCapacity:n * 2];
    for (size_t i = 0; i < n; i++) [h appendFormat:@"%02x", b[i]];
    return h;
}
static BOOL DSSyncEq(NSString *a, NSString *b) {   // مقارنة بزمن ثابت
    NSData *x = [a dataUsingEncoding:NSUTF8StringEncoding], *y = [b dataUsingEncoding:NSUTF8StringEncoding];
    if (x.length != y.length) return NO;
    const uint8_t *p = (const uint8_t *)x.bytes, *q = (const uint8_t *)y.bytes; uint8_t d = 0;
    for (NSUInteger i = 0; i < x.length; i++) d |= (uint8_t)(p[i] ^ q[i]);
    return d == 0;
}
static NSString *DSSyncSign(NSData *body, NSString *key) {
    NSData *k = [key dataUsingEncoding:NSUTF8StringEncoding];
    uint8_t mac[CC_SHA256_DIGEST_LENGTH];
    CCHmac(kCCHmacAlgSHA256, k.bytes, k.length, body.bytes, body.length, mac);
    return DSSyncHex(mac, sizeof mac);
}
static NSDictionary *DSPolicyAllowed(void) {   // المفتاح ← [أدنى, أعلى]
    return @{ @"DSAudioGain": @[@0, @4], @"DSAudioQoS": @[@0, @2], @"DSAudioBuf": @[@0, @2], @"DSAgoraAdv": @[@0, @2],
              @"DSKbNum": @[@0, @3], @"DSKbRev": @[@0, @1], @"DSKbNames": @[@0, @1], @"DSKbKeep": @[@0, @1],
              @"DSUltraMode": @[@0, @3], @"DSUltraAdaptive": @[@0, @1], @"DSUltraBoost": @[@0, @1] };
}
// بعد تغيير الإعدادات من الخادم: يعيد قراءة كل شي وتطبيقه فوراً
static void DSPolicyReload(void) {
    DSKbXLoad();
    gDSGain = DSAudioGainFactor(DSAudioGainIdx());
    DSAudioApplyAgoraGain(gDSLastEngine);
    DSAudioApplyAgoraAdv(gDSLastEngine);
    gQoSMode = (int)DSAudioQoSMode(); memset(gQoSSeen, 0, sizeof gQoSSeen);
    DSAudioApplyBuffer();
    DSUltraReload();   // آخراً: يرفع QoS للحد الأدنى إذا Ultra شغّال
}
static void DSSyncFinish(NSString *st, void (^done)(NSString *)) {
    dispatch_async(dispatch_get_main_queue(), ^{
        [NSUserDefaults.standardUserDefaults setObject:st forKey:@"DSSyncLast"];
        [NSNotificationCenter.defaultCenter postNotificationName:@"DSSyncChanged" object:nil];
        if (done) done(st);
    });
}
// يطبّق سياسة صالحة التوقيع (على الخيط الرئيسي)
static void DSPolicyHandle(NSDictionary *pol, void (^done)(NSString *)) {
    NSUserDefaults *d = NSUserDefaults.standardUserDefaults;
    NSNumber *gen = pol[@"gen"];
    if (![gen isKindOfClass:NSNumber.class]) { DSSyncFinish(@"السياسة بلا رقم gen — تجاهلتها", done); return; }
    NSInteger g = gen.integerValue, cur = [d integerForKey:@"DSSyncGen"];
    if (g <= cur) { DSSyncFinish([NSString stringWithFormat:@"لا جديد: gen %ld (المطبّق %ld)", (long)g, (long)cur], done); return; }
    NSArray *devs = pol[@"devices"];
    if ([devs isKindOfClass:NSArray.class] && devs.count) {
        BOOL mine = NO;
        for (id x in devs) if ([x isKindOfClass:NSString.class] && ([x isEqualToString:@"*"] || [(NSString *)x caseInsensitiveCompare:DSDeviceId()] == NSOrderedSame)) mine = YES;
        if (!mine) { DSSyncFinish(@"السياسة موجّهة لأجهزة ثانية — تجاهلتها", done); return; }
    }
    NSDictionary *allowed = DSPolicyAllowed(), *set = [pol[@"set"] isKindOfClass:NSDictionary.class] ? pol[@"set"] : @{};
    NSInteger n = 0;
    for (NSString *k in set) {
        NSArray *rng = allowed[k]; id v = set[k];
        if (!rng || ![v isKindOfClass:NSNumber.class]) continue;
        NSInteger x = [v integerValue];
        if (x < [rng[0] integerValue] || x > [rng[1] integerValue]) continue;
        [d setInteger:x forKey:k]; n++;
    }
    [d setInteger:g forKey:@"DSSyncGen"];
    DSPolicyReload();
    NSString *msg = [pol[@"message"] isKindOfClass:NSString.class] ? pol[@"message"] : nil;
    if (msg.length > 140) msg = [msg substringToIndex:140];
    NSDateFormatter *f = [NSDateFormatter new]; f.dateFormat = @"HH:mm";
    DSSyncFinish([NSString stringWithFormat:@"آخر مزامنة %@ · gen %ld · طُبّق %ld إعداد%@", [f stringFromDate:NSDate.date], (long)g, (long)n,
                  msg.length ? [@" · " stringByAppendingString:msg] : @""], done);
}
static void DSSyncNow(void (^done)(NSString *)) {
    NSString *base = DSSyncURL(), *key = DSSyncKeyStr();
    if (!base.length || !key.length) { DSSyncFinish(@"حدّد عنوان الخادم والمفتاح أولاً", done); return; }
    NSURLComponents *c = [NSURLComponents componentsWithString:base];
    if (!c || ![c.scheme.lowercaseString isEqualToString:@"https"] || !c.host.length) { DSSyncFinish(@"العنوان لازم يبدأ بـ https://", done); return; }
    NSString *path = c.path ?: @"";
    while ([path hasSuffix:@"/"]) path = [path substringToIndex:path.length - 1];
    c.path = [path stringByAppendingString:@"/api/v1/policy"];
    c.queryItems = @[[NSURLQueryItem queryItemWithName:@"device" value:DSDeviceId()], [NSURLQueryItem queryItemWithName:@"build" value:@"5.0.0"]];
    NSURL *url = c.URL;
    if (!url) { DSSyncFinish(@"عنوان غير صالح", done); return; }
    NSMutableURLRequest *r = [NSMutableURLRequest requestWithURL:url cachePolicy:NSURLRequestReloadIgnoringLocalCacheData timeoutInterval:10];
    [r setValue:@"application/json" forHTTPHeaderField:@"Accept"];
    NSURLSession *sess = [NSURLSession sessionWithConfiguration:NSURLSessionConfiguration.ephemeralSessionConfiguration];
    [[sess dataTaskWithRequest:r completionHandler:^(NSData *data, NSURLResponse *resp, NSError *err) {
        NSHTTPURLResponse *h = [resp isKindOfClass:NSHTTPURLResponse.class] ? (NSHTTPURLResponse *)resp : nil;
        if (err || !h) { DSSyncFinish([NSString stringWithFormat:@"فشل الاتصال: %@", err.localizedDescription ?: @"؟"], done); return; }
        if (h.statusCode != 200 || !data.length || data.length > 65536) { DSSyncFinish([NSString stringWithFormat:@"رد غير صالح (HTTP %ld)", (long)h.statusCode], done); return; }
        NSString *sig = [[h valueForHTTPHeaderField:@"X-Signature"] lowercaseString];
        if ([sig hasPrefix:@"sha256="]) sig = [sig substringFromIndex:7];
        if (!sig.length || !DSSyncEq(sig, DSSyncSign(data, key))) { DSSyncFinish(@"التوقيع غير صحيح — تجاهلت السياسة", done); return; }
        id j = [NSJSONSerialization JSONObjectWithData:data options:0 error:nil];
        if (![j isKindOfClass:NSDictionary.class]) { DSSyncFinish(@"صيغة السياسة غير صالحة", done); return; }
        dispatch_async(dispatch_get_main_queue(), ^{ DSPolicyHandle((NSDictionary *)j, done); });
    }] resume];
}
static dispatch_source_t gSyncTimer;
static void DSSyncBoot(void) {
    if (gSyncTimer) return;
    dispatch_after(dispatch_time(DISPATCH_TIME_NOW, 8 * NSEC_PER_SEC), dispatch_get_main_queue(), ^{ if (DSSyncIsOn()) DSSyncNow(nil); });
    gSyncTimer = dispatch_source_create(DISPATCH_SOURCE_TYPE_TIMER, 0, 0, dispatch_get_main_queue());
    dispatch_source_set_timer(gSyncTimer, dispatch_time(DISPATCH_TIME_NOW, 1800 * NSEC_PER_SEC), 1800 * NSEC_PER_SEC, 30 * NSEC_PER_SEC);
    dispatch_source_set_event_handler(gSyncTimer, ^{ if (DSSyncIsOn()) DSSyncNow(nil); });
    dispatch_resume(gSyncTimer);
}

#pragma mark - إعدادات الإرسال: رسالة ← آخر حقل دردشة كتبت فيه (بدون ID) — تكرار محدود
// رسالة واحدة تُرسل حتى 5 مرات، بفاصل 2 ثانية على الأقل (لا سرعة صفرية). يتوقف فوراً بزر الإيقاف أو أول ما لا تُرسل الرسالة فعلاً.
static NSString *DSSendMsgGet(void) { return [NSUserDefaults.standardUserDefaults stringForKey:@"DSSendMsg"] ?: @""; }
static NSInteger DSSendCount(void) {
    NSInteger n = [NSUserDefaults.standardUserDefaults integerForKey:@"DSSendCount"];
    return n < 1 ? 1 : (n > 5 ? 5 : n);
}
static NSInteger DSSendGap(void) {   // ثواني
    NSInteger n = [NSUserDefaults.standardUserDefaults integerForKey:@"DSSendGap"];
    return n < 2 ? 3 : (n > 10 ? 10 : n);
}
static BOOL gSendRun = NO;
static NSUInteger gSendGen = 0;
static NSInteger gSendDone = 0;
static void DSSendStop(void) { gSendRun = NO; gSendGen++; }
static void DSSendStep(NSUInteger gen, void (^status)(NSString *)) {
    if (!gSendRun || gen != gSendGen) return;
    __weak id tgt = DSQuickTarget();
    NSString *msg = DSSendMsgGet();
    if (!msg.length) { DSSendStop(); if (status) status(@"اكتب نص الرسالة أولاً"); return; }
    if (!DSQuickSendTo(tgt, msg)) { DSSendStop(); if (status) status(@"افتح حقل دردشة اللعبة واضغط فيه أولاً — توقّف"); return; }
    gSendDone++;
    dispatch_after(dispatch_time(DISPATCH_TIME_NOW, 300 * NSEC_PER_MSEC), dispatch_get_main_queue(), ^{
        if (gen != gSendGen) return;
        id f = tgt;
        NSString *rest = [f isKindOfClass:UITextField.class] ? ((UITextField *)f).text : ([f isKindOfClass:UITextView.class] ? ((UITextView *)f).text : nil);
        if (rest.length != 0) { DSSendStop(); if (status) status(@"⚠️ لم تُرسل — الحقل لم يتفرّغ، توقّفت"); return; }
        if (gSendDone >= DSSendCount()) { DSSendStop(); if (status) status([NSString stringWithFormat:@"✅ اكتمل: أُرسلت %ld", (long)gSendDone]); return; }
        if (status) status([NSString stringWithFormat:@"أُرسلت %ld من %ld…", (long)gSendDone, (long)DSSendCount()]);
        dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(DSSendGap() * NSEC_PER_SEC)), dispatch_get_main_queue(), ^{ DSSendStep(gen, status); });
    });
}
static void DSSendStart(void (^status)(NSString *)) {
    DSSendStop(); gSendRun = YES; gSendDone = 0;
    DSSendStep(gSendGen, status);
}

#pragma mark - قائمة ULTRA الثانية
static UIButton *DSUBtn(id target, NSString *t, NSString *ic, UIColor *c, SEL s) {
    UIButton *b = [UIButton buttonWithType:UIButtonTypeCustom];
    [b setTitle:t forState:UIControlStateNormal]; [b setTitleColor:c forState:UIControlStateNormal];
    [b setImage:DSIcon(ic, 12) forState:UIControlStateNormal]; b.tintColor = c;
    b.titleLabel.font = [UIFont systemFontOfSize:11.5 weight:UIFontWeightHeavy]; b.imageEdgeInsets = UIEdgeInsetsMake(0, -4, 0, 4);
    b.backgroundColor = [c colorWithAlphaComponent:0.15];
    b.layer.cornerRadius = 13; b.layer.cornerCurve = kCACornerCurveContinuous;
    b.layer.borderWidth = 1.3; b.layer.borderColor = [c colorWithAlphaComponent:0.75].CGColor;
    [b addTarget:target action:s forControlEvents:UIControlEventTouchUpInside];
    b.titleLabel.adjustsFontSizeToFitWidth = YES; b.titleLabel.minimumScaleFactor = 0.55; b.titleLabel.numberOfLines = 1;
    [b.heightAnchor constraintEqualToConstant:DSMenuBtnH()].active = YES;
    return b;
}
static UIStackView *DSURow(NSArray<UIView *> *items) {
    UIStackView *r = [[UIStackView alloc] initWithArrangedSubviews:items];
    r.distribution = UIStackViewDistributionFillEqually; r.spacing = 7;
    return r;
}
static UILabel *DSULabel(NSString *t, UIColor *c) {
    UILabel *l = [UILabel new]; l.text = t; l.textColor = c; l.numberOfLines = 0;
    l.font = [UIFont systemFontOfSize:11 weight:UIFontWeightMedium];
    return l;
}
static UIView *DSUCard(NSString *title, UIColor *c, NSArray<UIView *> *rows) {
    DSGradView *v = [DSGradView new];
    CAGradientLayer *gl = (CAGradientLayer *)v.layer;
    gl.colors = @[(id)[c colorWithAlphaComponent:0.22].CGColor, (id)[DSHex(kPanel) colorWithAlphaComponent:0.96].CGColor, (id)DSHex(kBG).CGColor];
    gl.startPoint = CGPointMake(0, 0); gl.endPoint = CGPointMake(1, 1);
    v.layer.cornerRadius = 16; v.layer.cornerCurve = kCACornerCurveContinuous;
    v.layer.borderWidth = 1.3; v.layer.borderColor = [c colorWithAlphaComponent:0.65].CGColor;
    UILabel *t = [UILabel new]; t.text = [@"▍ " stringByAppendingString:title]; t.textColor = DSHex(kText);
    t.font = [UIFont systemFontOfSize:12.5 weight:UIFontWeightHeavy];
    NSMutableArray *all = [NSMutableArray arrayWithObject:t]; [all addObjectsFromArray:rows];
    UIStackView *st = [[UIStackView alloc] initWithArrangedSubviews:all];
    st.axis = UILayoutConstraintAxisVertical; st.spacing = 8; st.translatesAutoresizingMaskIntoConstraints = NO;
    [v addSubview:st];
    [NSLayoutConstraint activateConstraints:@[
        [st.topAnchor constraintEqualToAnchor:v.topAnchor constant:10], [st.bottomAnchor constraintEqualToAnchor:v.bottomAnchor constant:-10],
        [st.leadingAnchor constraintEqualToAnchor:v.leadingAnchor constant:10], [st.trailingAnchor constraintEqualToAnchor:v.trailingAnchor constant:-10]]];
    return v;
}

@implementation DSUltraVC {
    UIStackView *_main; UILabel *_toast;
}
- (UIStatusBarStyle)preferredStatusBarStyle { return UIStatusBarStyleLightContent; }

- (void)viewDidLoad {
    [super viewDidLoad];
    self.view.backgroundColor = DSHex(kBG);
    self.overrideUserInterfaceStyle = UIUserInterfaceStyleDark;
    UILayoutGuide *g = self.view.safeAreaLayoutGuide;
    UILabel *title = [UILabel new]; title.text = @"ULTRA ⚡  صوت + مزامنة";
    title.textColor = DSHex(kGreen); title.font = DSMono(15, UIFontWeightHeavy); DSGlow(title.layer, DSHex(kGreen), 6);
    UIButton *close = [UIButton buttonWithType:UIButtonTypeSystem];
    [close setTitle:@"✕ رجوع" forState:UIControlStateNormal]; close.tintColor = DSHex(kRed);
    close.titleLabel.font = [UIFont systemFontOfSize:13 weight:UIFontWeightHeavy];
    [close addTarget:self action:@selector(closeTap) forControlEvents:UIControlEventTouchUpInside];
    UIStackView *head = [[UIStackView alloc] initWithArrangedSubviews:@[title, [UIView new], close]];
    head.alignment = UIStackViewAlignmentCenter; head.translatesAutoresizingMaskIntoConstraints = NO;
    [self.view addSubview:head];
    UIScrollView *sv = [UIScrollView new]; sv.translatesAutoresizingMaskIntoConstraints = NO;
    sv.alwaysBounceVertical = YES; sv.showsVerticalScrollIndicator = NO; sv.keyboardDismissMode = UIScrollViewKeyboardDismissModeOnDrag;
    [self.view addSubview:sv];
    _main = [UIStackView new]; _main.axis = UILayoutConstraintAxisVertical; _main.spacing = 10; _main.translatesAutoresizingMaskIntoConstraints = NO;
    [sv addSubview:_main];
    [NSLayoutConstraint activateConstraints:@[
        [head.topAnchor constraintEqualToAnchor:g.topAnchor constant:8],
        [head.leadingAnchor constraintEqualToAnchor:g.leadingAnchor constant:14], [head.trailingAnchor constraintEqualToAnchor:g.trailingAnchor constant:-14],
        [sv.topAnchor constraintEqualToAnchor:head.bottomAnchor constant:6], [sv.bottomAnchor constraintEqualToAnchor:g.bottomAnchor],
        [sv.leadingAnchor constraintEqualToAnchor:g.leadingAnchor], [sv.trailingAnchor constraintEqualToAnchor:g.trailingAnchor],
        [_main.topAnchor constraintEqualToAnchor:sv.contentLayoutGuide.topAnchor constant:6],
        [_main.bottomAnchor constraintEqualToAnchor:sv.contentLayoutGuide.bottomAnchor constant:-16],
        [_main.leadingAnchor constraintEqualToAnchor:sv.frameLayoutGuide.leadingAnchor constant:14],
        [_main.trailingAnchor constraintEqualToAnchor:sv.frameLayoutGuide.trailingAnchor constant:-14]]];
    _toast = [UILabel new]; _toast.backgroundColor = DSHex(kPanel); _toast.textColor = DSHex(kGreen); _toast.textAlignment = NSTextAlignmentCenter;
    _toast.font = DSMono(12, UIFontWeightBold); _toast.layer.cornerRadius = 10; _toast.layer.borderWidth = 1; _toast.layer.borderColor = DSHex(kGreen).CGColor;
    _toast.clipsToBounds = YES; _toast.alpha = 0; _toast.numberOfLines = 3;
    _toast.translatesAutoresizingMaskIntoConstraints = NO; [self.view addSubview:_toast];
    [NSLayoutConstraint activateConstraints:@[
        [_toast.centerXAnchor constraintEqualToAnchor:self.view.centerXAnchor], [_toast.bottomAnchor constraintEqualToAnchor:g.bottomAnchor constant:-24],
        [_toast.widthAnchor constraintLessThanOrEqualToAnchor:self.view.widthAnchor constant:-40], [_toast.widthAnchor constraintGreaterThanOrEqualToConstant:200],
        [_toast.heightAnchor constraintGreaterThanOrEqualToConstant:38]]];
    [NSNotificationCenter.defaultCenter addObserver:self selector:@selector(rebuild) name:@"DSSyncChanged" object:nil];
    [self rebuild];
}
- (void)dealloc { [NSNotificationCenter.defaultCenter removeObserver:self]; }

- (void)toast:(NSString *)t {
    _toast.text = [NSString stringWithFormat:@"  %@  ", t];
    [_toast.layer removeAllAnimations];
    [UIView animateWithDuration:0.2 animations:^{ self->_toast.alpha = 1; } completion:^(BOOL f) {
        [UIView animateWithDuration:0.3 delay:2.4 options:0 animations:^{ self->_toast.alpha = 0; } completion:nil];
    }];
}
- (void)closeTap { [self dismissViewControllerAnimated:YES completion:nil]; }

- (NSString *)liveStatus {
    NSString *ping = @"PING —";
    if (gUltraRttN > 0) { double ms = gUltraRtt[gUltraRttN - 1]; if (ms >= 0) ping = [NSString stringWithFormat:@"PING %.0fms", ms]; }
    return [NSString stringWithFormat:@"الآن: %@ · %@", DSUltraModeName(gUltraEff), ping];
}

- (void)rebuild {
    for (UIView *v in [_main.arrangedSubviews copy]) { [_main removeArrangedSubview:v]; [v removeFromSuperview]; }
    UIColor *on = DSHex(kGreen), *off = DSHex(kDim);
    // ---- صوت ULTRA
    UIButton *bMode = DSUBtn(self, DSUltraTitle(), @"bolt.fill", DSUltraIsOn() ? on : off, @selector(modeTap:));
    UIButton *bAdp = DSUBtn(self, DSUltraAdaptive() ? @"تكيّف تلقائي: ON" : @"تكيّف تلقائي: OFF", @"slider.horizontal.3", DSUltraAdaptive() ? DSHex(kCyan) : off, @selector(adaptTap:));
    UIButton *bBoost = DSUBtn(self, DSUltraBoostOn() ? @"تسريع العملية: ON" : @"تسريع العملية: OFF", @"speedometer", DSUltraBoostOn() ? DSHex(kAmber) : off, @selector(boostTap:));
    UIButton *bStat = DSUBtn(self, [self liveStatus], @"waveform.path.ecg", DSHex(kPurple), @selector(statusTap:));
    UILabel *info = DSULabel(@"متوازن: مخزن 40ms (أأمن ضد القطع) · سريع: 0–120ms · أقصى: 0–60ms + تسريع كامل.\nالتكيّف يقيس PING كل 6 ثوانٍ وينزّل الوضع فوراً إذا النت ضعيف ويرجّعه بعد 20 ثانية ثبات. «تسريع العملية» أثره بسيط على iOS. خروج الروم ودخوله يرجّع الإعدادات الأصلية بعد إطفاء Ultra.", DSHex(kDim));
    [_main addArrangedSubview:DSUCard(@"صوت ULTRA", on, @[DSURow(@[bMode, bAdp]), DSURow(@[bBoost, bStat]), info])];
    // ---- مزامنة الخادم الإداري
    UIColor *cy = DSHex(kCyan);
    UIButton *bSyncOn = DSUBtn(self, DSSyncIsOn() ? @"مزامنة تلقائية: ON" : @"مزامنة تلقائية: OFF", @"arrow.triangle.2.circlepath", DSSyncIsOn() ? cy : off, @selector(syncOnTap:));
    UIButton *bSyncNow = DSUBtn(self, @"مزامنة الآن", @"icloud.and.arrow.down", cy, @selector(syncNowTap:));
    UIButton *bUrl = DSUBtn(self, DSSyncURL().length ? @"عنوان الخادم ✓" : @"عنوان الخادم", @"link", cy, @selector(urlTap:));
    UIButton *bKey = DSUBtn(self, DSSyncKeyStr().length ? @"مفتاح التوقيع ✓" : @"مفتاح التوقيع", @"key.fill", cy, @selector(keyTap:));
    UIButton *bId = DSUBtn(self, @"نسخ معرّف الجهاز", @"doc.on.doc", DSHex(kGold), @selector(idTap:));
    UILabel *st = DSULabel([NSString stringWithFormat:@"%@\nمعرّف الجهاز: %@\ngen المطبّق: %ld", DSSyncStatus(), DSDeviceId(), (long)[NSUserDefaults.standardUserDefaults integerForKey:@"DSSyncGen"]], DSHex(kText));
    UILabel *sinfo = DSULabel(@"الخادم يوقّع جسم الرد بـ HMAC-SHA256 (ترويسة X-Signature) ويستلم منك معرّف الجهاز ورقم الإصدار فقط. https فقط، وgen لازم يزيد. السياسة تغيّر إعدادات الأداة المسموحة (التقوية، QoS، المخزن، Ultra، الكيبورد) ولا تقدر تحجب الأداة.", DSHex(kDim));
    [_main addArrangedSubview:DSUCard(@"مزامنة الخادم الإداري", cy, @[DSURow(@[bSyncOn, bSyncNow]), DSURow(@[bUrl, bKey]), DSURow(@[bId, [UIView new]]), st, sinfo])];
    // ---- الإرسال للّعبة (بديل «الاوجود») + رسائل جاهزة
    UIColor *pu = DSHex(kPurple);
    UIButton *bDs = DSUBtn(self, DSDigitSendTitle(), @"number.circle.fill", DSDigitSendIsOn() ? on : off, @selector(dsToggleTap:));
    UIButton *bDn = DSUBtn(self, [NSString stringWithFormat:@"عدد الخانات: %ld", (long)DSDigitSendN()], @"textformat.123", pu, @selector(dsCountTap:));
    UIButton *bTp = DSUBtn(self, @"رسائل جاهزة", @"text.bubble", pu, @selector(tplTap:));
    UIButton *bMd = DSUBtn(self, DSQuickModesTitle(), @"text.badge.checkmark", DSQuickModesOn() ? on : off, @selector(modesTap:));
    UILabel *dinfo = DSULabel(@"إرسال عند اكتمال الأرقام: لما تكتب بحقل دردشة اللعبة (أو بصندوق «الكتابة السريعة») أرقاماً بعدد الخانات المحدد تنرسل تلقائياً — بديل «الاوجود». رسائل جاهزة: تضغط الرسالة فتنرسل مرة وحدة لآخر حقل دردشة فتحته. أوضاع الكتابة السريعة: ترتيب/تدبيل/عكس/أسماء تُطبَّق على رسالتك قبل الإرسال.", DSHex(kDim));
    [_main addArrangedSubview:DSUCard(@"الإرسال للّعبة", pu, @[DSURow(@[bDs, bDn]), DSURow(@[bTp, bMd]), dinfo])];
    // ---- إعدادات الإرسال (رسالة ← دردشة اللعبة، تكرار محدود)
    UIColor *am = DSHex(kAmber);
    NSString *msgNow = DSSendMsgGet();
    UIButton *bSm = DSUBtn(self, msgNow.length ? [NSString stringWithFormat:@"الرسالة: %@", msgNow.length > 18 ? [[msgNow substringToIndex:18] stringByAppendingString:@"…"] : msgNow] : @"نص الرسالة", @"square.and.pencil", am, @selector(sendMsgTap:));
    UIButton *bSc = DSUBtn(self, [NSString stringWithFormat:@"التكرار: %ld (1–5)", (long)DSSendCount()], @"repeat", am, @selector(sendCountTap:));
    UIButton *bSg = DSUBtn(self, [NSString stringWithFormat:@"الفاصل: %lds (2–10)", (long)DSSendGap()], @"timer", am, @selector(sendGapTap:));
    UIButton *bGo = DSUBtn(self, @"إطلاق ⚡", @"paperplane.fill", on, @selector(sendGoTap:));
    UIButton *bSt = DSUBtn(self, @"إيقاف ■", @"stop.fill", DSHex(kRed), @selector(sendStopTap:));
    UILabel *sinf2 = DSULabel(@"الإرسال لآخر حقل دردشة كتبت فيه باللعبة (بدون ID). الحد الأقصى 5 مرات وأقل فاصل ثانيتين، ويتوقف تلقائياً إذا الرسالة ما انرسلت فعلاً. تمر على أوضاع الكتابة السريعة إذا مفعّلة.", DSHex(kDim));
    [_main addArrangedSubview:DSUCard(@"إعدادات الإرسال", am, @[DSURow(@[bSm]), DSURow(@[bSc, bSg]), DSURow(@[bGo, bSt]), sinf2])];
    // ---- ميزات أخرى
    UIButton *bKeep = DSUBtn(self, gKbKeep ? @"إبقاء الكيبورد بعد الإرسال: ON" : @"إبقاء الكيبورد بعد الإرسال: OFF", @"keyboard", gKbKeep ? on : off, @selector(keepTap:));
    UILabel *kinfo = DSULabel(@"يعمل مع «الكتابة السريعة/حساسية الكيبورد»: بعد ما الأداة ترسل الرسالة، ترجّع التركيز للحقل إذا اللعبة سحبته.", DSHex(kDim));
    [_main addArrangedSubview:DSUCard(@"ميزات أخرى", DSHex(kAmber), @[DSURow(@[bKeep]), kinfo])];
}

- (void)modeTap:(UIButton *)b {
    DSUltraModeCycle(); [self rebuild];
    NSInteger m = DSUltraMode();
    [self toast:(m == 0 ? @"Ultra متوقف — للرجوع الكامل اخرج وادخل الروم" : [NSString stringWithFormat:@"Ultra: %@ — يُطبَّق على روم الصوت الحالي", DSUltraModeName(m)])];
}
- (void)adaptTap:(UIButton *)b {
    BOOL on = !DSUltraAdaptive();
    [NSUserDefaults.standardUserDefaults setBool:on forKey:@"DSUltraAdaptive"];
    gUltraRttN = 0; gUltraLastSwitch = 0; DSUltraSetEff((int)DSUltraMode());
    [self rebuild];
    [self toast:(on ? @"التكيّف مفعّل: يقيس PING كل 6 ثوانٍ ويضبط الوضع" : @"التكيّف متوقف: يثبت على وضعك")];
}
- (void)boostTap:(UIButton *)b {
    BOOL on = !DSUltraBoostOn();
    [NSUserDefaults.standardUserDefaults setBool:on forKey:@"DSUltraBoost"];
    DSUltraBoostApply(on); [self rebuild];
    [self toast:(on ? @"تسريع العملية: ON (نشاط حساس للتأخير)" : @"تسريع العملية: OFF")];
}
- (void)statusTap:(UIButton *)b { [self rebuild]; [self toast:[self liveStatus]]; }
- (void)syncOnTap:(UIButton *)b {
    BOOL on = !DSSyncIsOn();
    [NSUserDefaults.standardUserDefaults setBool:on forKey:@"DSSyncOn"];
    [self rebuild];
    [self toast:(on ? @"المزامنة التلقائية: عند فتح اللعبة وكل 30 دقيقة" : @"المزامنة التلقائية متوقفة")];
}
- (void)syncNowTap:(UIButton *)b {
    [self toast:@"جاري المزامنة…"];
    __weak typeof(self) ws = self;
    DSSyncNow(^(NSString *st) { [ws toast:st]; });
}
- (void)editSetting:(NSString *)key title:(NSString *)title ph:(NSString *)ph secure:(BOOL)sec {
    UIAlertController *a = [UIAlertController alertControllerWithTitle:title message:nil preferredStyle:UIAlertControllerStyleAlert];
    [a addTextFieldWithConfigurationHandler:^(UITextField *t) {
        t.text = sec ? @"" : [NSUserDefaults.standardUserDefaults stringForKey:key];
        t.placeholder = ph; t.secureTextEntry = sec; t.keyboardType = sec ? UIKeyboardTypeDefault : UIKeyboardTypeURL;
        t.autocapitalizationType = UITextAutocapitalizationTypeNone; t.autocorrectionType = UITextAutocorrectionTypeNo;
    }];
    [a addAction:[UIAlertAction actionWithTitle:@"إلغاء" style:UIAlertActionStyleCancel handler:nil]];
    [a addAction:[UIAlertAction actionWithTitle:@"حفظ" style:UIAlertActionStyleDefault handler:^(UIAlertAction *x) {
        NSString *v = [a.textFields.firstObject.text stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceAndNewlineCharacterSet];
        if (v.length) [NSUserDefaults.standardUserDefaults setObject:v forKey:key]; else [NSUserDefaults.standardUserDefaults removeObjectForKey:key];
        [self rebuild]; [self toast:(v.length ? @"تم الحفظ" : @"تم المسح")];
    }]];
    [self presentViewController:a animated:YES completion:nil];
}
- (void)urlTap:(UIButton *)b { [self editSetting:@"DSSyncURL" title:@"عنوان الخادم (https)" ph:@"https://example.com" secure:NO]; }
- (void)keyTap:(UIButton *)b { [self editSetting:@"DSSyncKey" title:@"مفتاح التوقيع (سرّي)" ph:@"نفس مفتاح الخادم" secure:YES]; }
- (void)idTap:(UIButton *)b { UIPasteboard.generalPasteboard.string = DSDeviceId(); [self toast:@"نُسخ معرّف الجهاز (استخدمه بحقل devices بالسياسة)"]; }
- (void)dsToggleTap:(UIButton *)b {
    DSDigitSendToggle(); [self rebuild];
    [self toast:(DSDigitSendIsOn() ? @"الإرسال عند اكتمال الأرقام: ON" : @"الإرسال عند اكتمال الأرقام: OFF")];
}
- (void)dsCountTap:(UIButton *)b {
    UIAlertController *a = [UIAlertController alertControllerWithTitle:@"عدد الخانات" message:@"الإرسال التلقائي عند اكتمال هذا العدد من الأرقام" preferredStyle:UIAlertControllerStyleAlert];
    NSArray *presets = @[@[@2, @"2 — عشرات"], @[@3, @"3 — مئات"], @[@4, @"4 — آلاف"], @[@5, @"5 — عشرات الآلاف"]];
    for (NSArray *pr in presets) {
        NSInteger n = [pr[0] integerValue];
        [a addAction:[UIAlertAction actionWithTitle:pr[1] style:UIAlertActionStyleDefault handler:^(UIAlertAction *x) { DSDigitSendSetN(n); [self rebuild]; [self toast:[NSString stringWithFormat:@"عدد الخانات: %ld", (long)n]]; }]];
    }
    [a addAction:[UIAlertAction actionWithTitle:@"عدد مخصص…" style:UIAlertActionStyleDefault handler:^(UIAlertAction *x) {
        UIAlertController *c = [UIAlertController alertControllerWithTitle:@"عدد مخصص (1–40)" message:nil preferredStyle:UIAlertControllerStyleAlert];
        [c addTextFieldWithConfigurationHandler:^(UITextField *t) { t.keyboardType = UIKeyboardTypeNumberPad; t.text = [NSString stringWithFormat:@"%ld", (long)DSDigitSendN()]; }];
        [c addAction:[UIAlertAction actionWithTitle:@"إلغاء" style:UIAlertActionStyleCancel handler:nil]];
        [c addAction:[UIAlertAction actionWithTitle:@"تطبيق" style:UIAlertActionStyleDefault handler:^(UIAlertAction *y) {
            NSInteger n = c.textFields.firstObject.text.integerValue;
            if (n >= 1) { DSDigitSendSetN(n); [self rebuild]; [self toast:[NSString stringWithFormat:@"عدد الخانات: %ld", (long)DSDigitSendN()]]; }
        }]];
        [self presentViewController:c animated:YES completion:nil];
    }]];
    [a addAction:[UIAlertAction actionWithTitle:@"إلغاء" style:UIAlertActionStyleCancel handler:nil]];
    [self presentViewController:a animated:YES completion:nil];
}
- (void)modesTap:(UIButton *)b {
    NSUserDefaults *d = NSUserDefaults.standardUserDefaults;
    [d setBool:![d objectForKey:@"DSQuickModes"] ? NO : ![d boolForKey:@"DSQuickModes"] forKey:@"DSQuickModes"];
    [self rebuild];
    [self toast:(DSQuickModesOn() ? @"الأوضاع تُطبَّق على الكتابة السريعة" : @"الكتابة السريعة بدون أوضاع")];
}
// رسائل جاهزة: ضغطة وحدة = إرسال مرة وحدة لآخر حقل دردشة (بدون تكرار)
- (void)tplTap:(UIButton *)b {
    NSUserDefaults *d = NSUserDefaults.standardUserDefaults;
    NSArray<NSString *> *list = [d arrayForKey:@"DSQuickTpl"] ?: @[];
    UIAlertController *a = [UIAlertController alertControllerWithTitle:@"رسائل جاهزة" message:(list.count ? @"اضغط رسالة لإرسالها مرة وحدة" : @"ما عندك رسائل محفوظة بعد") preferredStyle:UIAlertControllerStyleAlert];
    for (NSString *m in list) {
        NSString *t = m.length > 38 ? [[m substringToIndex:38] stringByAppendingString:@"…"] : m;
        [a addAction:[UIAlertAction actionWithTitle:t style:UIAlertActionStyleDefault handler:^(UIAlertAction *x) {
            __weak id tgt = DSQuickTarget();
            if (!DSQuickSendTo(tgt, m)) { [self toast:@"افتح حقل دردشة اللعبة واضغط فيه أولاً"]; return; }
            dispatch_after(dispatch_time(DISPATCH_TIME_NOW, 300 * NSEC_PER_MSEC), dispatch_get_main_queue(), ^{
                id f = tgt; NSString *rest = [f isKindOfClass:UITextField.class] ? ((UITextField *)f).text : ([f isKindOfClass:UITextView.class] ? ((UITextView *)f).text : nil);
                [self toast:(rest.length == 0 ? @"✅ أُرسلت" : @"⚠️ لم تُرسل — الحقل لم يتفرّغ")];
            });
        }]];
    }
    if (list.count < 6) [a addAction:[UIAlertAction actionWithTitle:@"➕ إضافة رسالة" style:UIAlertActionStyleDefault handler:^(UIAlertAction *x) {
        UIAlertController *c = [UIAlertController alertControllerWithTitle:@"رسالة جديدة" message:nil preferredStyle:UIAlertControllerStyleAlert];
        [c addTextFieldWithConfigurationHandler:^(UITextField *t) { t.placeholder = @"نص الرسالة"; }];
        [c addAction:[UIAlertAction actionWithTitle:@"إلغاء" style:UIAlertActionStyleCancel handler:nil]];
        [c addAction:[UIAlertAction actionWithTitle:@"حفظ" style:UIAlertActionStyleDefault handler:^(UIAlertAction *y) {
            NSString *v = [c.textFields.firstObject.text stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceAndNewlineCharacterSet];
            if (!v.length) return;
            if (v.length > 200) v = [v substringToIndex:200];
            [d setObject:[list arrayByAddingObject:v] forKey:@"DSQuickTpl"];
            [self toast:@"تم حفظ الرسالة"];
        }]];
        [self presentViewController:c animated:YES completion:nil];
    }]];
    if (list.count) [a addAction:[UIAlertAction actionWithTitle:@"🗑 مسح الكل" style:UIAlertActionStyleDestructive handler:^(UIAlertAction *x) { [d removeObjectForKey:@"DSQuickTpl"]; [self toast:@"تم المسح"]; }]];
    [a addAction:[UIAlertAction actionWithTitle:@"إغلاق" style:UIAlertActionStyleCancel handler:nil]];
    [self presentViewController:a animated:YES completion:nil];
}
- (void)sendMsgTap:(UIButton *)b {
    UIAlertController *a = [UIAlertController alertControllerWithTitle:@"نص الرسالة" message:@"تنرسل لدردشة اللعبة" preferredStyle:UIAlertControllerStyleAlert];
    [a addTextFieldWithConfigurationHandler:^(UITextField *t) { t.text = DSSendMsgGet(); t.placeholder = @"اكتب الرسالة"; }];
    [a addAction:[UIAlertAction actionWithTitle:@"إلغاء" style:UIAlertActionStyleCancel handler:nil]];
    [a addAction:[UIAlertAction actionWithTitle:@"حفظ" style:UIAlertActionStyleDefault handler:^(UIAlertAction *x) {
        NSString *v = [a.textFields.firstObject.text stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceAndNewlineCharacterSet];
        if (v.length > 200) v = [v substringToIndex:200];
        if (v.length) [NSUserDefaults.standardUserDefaults setObject:v forKey:@"DSSendMsg"]; else [NSUserDefaults.standardUserDefaults removeObjectForKey:@"DSSendMsg"];
        [self rebuild]; [self toast:(v.length ? @"تم حفظ الرسالة" : @"تم المسح")];
    }]];
    [self presentViewController:a animated:YES completion:nil];
}
- (void)sendCountTap:(UIButton *)b {   // 1 ← 2 ← 3 ← 4 ← 5 ← 1
    [NSUserDefaults.standardUserDefaults setInteger:(DSSendCount() % 5) + 1 forKey:@"DSSendCount"];
    [self rebuild];
}
- (void)sendGapTap:(UIButton *)b {     // 2 ← 3 ← 5 ← 10 ← 2 ثانية
    NSInteger g = DSSendGap(), nx = g < 3 ? 3 : (g < 5 ? 5 : (g < 10 ? 10 : 2));
    [NSUserDefaults.standardUserDefaults setInteger:nx forKey:@"DSSendGap"];
    [self rebuild];
}
- (void)sendGoTap:(UIButton *)b {
    __weak typeof(self) ws = self;
    [self toast:[NSString stringWithFormat:@"إطلاق: %ld × كل %lds", (long)DSSendCount(), (long)DSSendGap()]];
    DSSendStart(^(NSString *st) { [ws toast:st]; });
}
- (void)sendStopTap:(UIButton *)b { DSSendStop(); [self toast:@"تم الإيقاف"]; }
- (void)keepTap:(UIButton *)b {
    BOOL on = !gKbKeep;
    [NSUserDefaults.standardUserDefaults setBool:on forKey:@"DSKbKeep"];
    gKbKeep = on; [self rebuild];
    [self toast:(on ? @"إبقاء الكيبورد مفعّل" : @"إبقاء الكيبورد متوقف")];
}
@end

#pragma mark - AUDIO PRO (المنيو الثالث): تقليل تأخير + معالجة صوت
// معالجة الصوت نفسها (AudioPro.inc) تعمل على المخرج النهائي بنفس نقطة «تقوية الصوت» (DSRenderWrap)، وتضيف ~0ms.
// تقليل التأخير هنا يجمع أزرار موجودة أصلاً (Agora/المخزن/QoS/Ultra) + ثلاث ميزات جديدة:
//   مطابقة تردد الجهاز 48kHz (يتجنب إعادة التعيين)، سقف تأخير الشبكة بالمللي ثانية، وقياس حي لتأخير مخرج الجهاز.
static NSUserDefaults *DSAPD(void) { return NSUserDefaults.standardUserDefaults; }
static float DSAPF(NSString *k, float d) { id o = [DSAPD() objectForKey:k]; return o ? [o floatValue] : d; }

static const struct { float bass, mid, treb, comp, gate; int hpf; } kAPPre[] = {
    { 0, 0, 0, 0, 0, 0 },          // 0 مخصص (يبقي قيم المنزلقات الحالية)
    { -2, 4, 2, 0.35f, -52, 1 },   // 1 وضوح الكلام
    { 0, 2, 0, 0.75f, -55, 1 },    // 2 موازنة الأصوات (الهادئ يرتفع والعالي يهبط)
    { 7, 0, 1, 0.20f, 0, 0 },      // 3 باس
    { -2, 1, -4, 0.90f, -50, 1 },  // 4 ليلي (ديناميكية قليلة وحدّة ناعمة)
};
#define DS_AP_PRE_N 5
static NSArray<NSString *> *DSAPPreNames(void) { return @[@"مخصص", @"وضوح الكلام", @"موازنة الأصوات", @"باس", @"ليلي"]; }

static NSInteger DSAPPreset(void) { NSInteger p = [DSAPD() integerForKey:@"DSAPPreset"]; return (p < 0 || p >= DS_AP_PRE_N) ? 0 : p; }
static void DSAPSave(void) {
    NSUserDefaults *d = DSAPD();
    [d setBool:gAP.on != 0 forKey:@"DSAPOn"];
    [d setFloat:gAP.bass forKey:@"DSAPBass"]; [d setFloat:gAP.mid forKey:@"DSAPMid"]; [d setFloat:gAP.treb forKey:@"DSAPTreb"];
    [d setFloat:gAP.comp forKey:@"DSAPComp"]; [d setFloat:gAP.gate forKey:@"DSAPGate"];
    [d setBool:gAP.hpf != 0 forKey:@"DSAPHpf"]; [d setBool:gAP.mono != 0 forKey:@"DSAPMono"];
}
static void DSAPLoad(void) {
    NSUserDefaults *d = DSAPD();
    gAP.bass = DSAPF(@"DSAPBass", 0); gAP.mid = DSAPF(@"DSAPMid", 0); gAP.treb = DSAPF(@"DSAPTreb", 0);
    gAP.comp = DSAPF(@"DSAPComp", 0); gAP.gate = DSAPF(@"DSAPGate", 0);
    gAP.hpf = [d boolForKey:@"DSAPHpf"]; gAP.mono = [d boolForKey:@"DSAPMono"];
    gAP.on = [d boolForKey:@"DSAPOn"]; gAP.gen++;
}
static void DSAPSetPreset(NSInteger p) {
    if (p < 0 || p >= DS_AP_PRE_N) p = 0;
    if (p > 0) {
        gAP.bass = kAPPre[p].bass; gAP.mid = kAPPre[p].mid; gAP.treb = kAPPre[p].treb;
        gAP.comp = kAPPre[p].comp; gAP.gate = kAPPre[p].gate; gAP.hpf = kAPPre[p].hpf;
    }
    gAP.gen++; [DSAPD() setInteger:p forKey:@"DSAPPreset"]; DSAPSave();
}

static BOOL DSAPSR48(void) { return [DSAPD() boolForKey:@"DSAPSR48"]; }
static NSInteger DSAPNetCap(void) { NSInteger c = [DSAPD() integerForKey:@"DSAPNetCap"]; return (c < 0 || c > 4) ? 0 : c; }
static NSString *DSAPNetCapTitle(void) {
    return [NSString stringWithFormat:@"سقف تأخير الشبكة: %@", @[@"OFF", @"60ms", @"100ms", @"150ms", @"250ms"][DSAPNetCap()]];
}
static void DSAPApplySessionNow(void) {
    if (!DSAPSR48()) return;
    dispatch_async(dispatch_get_main_queue(), ^{
        NSError *err = nil;
        [[AVAudioSession sharedInstance] setPreferredSampleRate:48000 error:&err];
        NSLog(@"[AflatoonSuite] preferred sample rate 48000 -> %@ (actual %.0f)", err ? err.localizedDescription : @"ok", AVAudioSession.sharedInstance.sampleRate);
    });
}
static void DSAPApplySession(void) {   // اللعبة قد تعيد ضبط الجلسة، فنعيد الطلب بعد ثوانٍ
    if (!DSAPSR48()) return;
    DSAPApplySessionNow();
    for (NSNumber *s in @[@3.5, @8]) dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(s.doubleValue * NSEC_PER_SEC)), dispatch_get_main_queue(), ^{ DSAPApplySessionNow(); });
}
// سقف تأخير مخزن الشبكة (rtc.max_playout_delay) — مفتاح Agora بنفس دلالة WebRTC (min=0 = اعرض أسرع ما يمكن). أصغر = تأخير أقل وتقطيع أكثر.
static void DSAPApplyAgora(id engine) {
    NSInteger c = DSAPNetCap(); if (!engine || c <= 0) return;
    static const int ms[5] = { 0, 60, 100, 150, 250 };
    DSAgoraSetParameters(engine, @"{\"rtc.min_playout_delay\":0}");
    DSAgoraSetParameters(engine, [NSString stringWithFormat:@"{\"rtc.max_playout_delay\":%d}", ms[c]]);
}
static void DSAPBoot(void) {
    DSAPLoad();
    DSAPApplySession();
    [[NSNotificationCenter defaultCenter] addObserverForName:AVAudioSessionRouteChangeNotification object:nil queue:nil usingBlock:^(NSNotification *n) {
        if (!DSAPSR48()) return;
        dispatch_after(dispatch_time(DISPATCH_TIME_NOW, 500 * NSEC_PER_MSEC), dispatch_get_main_queue(), ^{ DSAPApplySessionNow(); });
    }];
}

// قياس حي من نظام iOS نفسه (أرقام حقيقية وليست تقديراً): تأخير المخرج + مخزن IO + التردد + نوع المسار
static NSString *DSAPMeterText(void) {
    AVAudioSession *as = AVAudioSession.sharedInstance;
    NSString *pt = as.currentRoute.outputs.firstObject.portType ?: @"";
    BOOL bt = [pt isEqualToString:AVAudioSessionPortBluetoothA2DP] || [pt isEqualToString:AVAudioSessionPortBluetoothHFP] || [pt isEqualToString:AVAudioSessionPortBluetoothLE];
    NSString *route = bt ? @"بلوتوث" : [pt isEqualToString:AVAudioSessionPortBuiltInSpeaker] ? @"سماعة الجهاز" : [pt isEqualToString:AVAudioSessionPortHeadphones] ? @"سماعات سلكية" : (pt.length ? pt : @"—");
    NSString *s = [NSString stringWithFormat:@"تأخير مخرج الجهاز: %.1f ms · مخزن IO: %.1f ms · %.0f Hz\nالمسار: %@", as.outputLatency * 1000.0, as.IOBufferDuration * 1000.0, as.sampleRate, route];
    if (bt) s = [s stringByAppendingString:@"\n⚠ البلوتوث يضيف عادةً 100–250ms ولا تقدر الأداة تلغيها — السلك أسرع."];
    return s;
}

static NSString *DSAPSliderTitle(int t) {
    switch (t) { case 1: return @"باس"; case 2: return @"وضوح الصوت"; case 3: return @"حدّة (Treble)"; case 4: return @"موازنة الأصوات"; default: return @"بوابة الضوضاء"; }
}
static NSString *DSAPSliderText(int t, float v) {
    if (t <= 3) return [NSString stringWithFormat:@"%@: %+.0f dB", DSAPSliderTitle(t), roundf(v)];
    if (t == 4) return [NSString stringWithFormat:@"%@: %.0f%%", DSAPSliderTitle(t), v];
    return [NSString stringWithFormat:@"%@: %@", DSAPSliderTitle(t), v <= -64 ? @"OFF" : [NSString stringWithFormat:@"%.0f dB", roundf(v)]];
}

@implementation DSAudioProVC {
    UIStackView *_main; UILabel *_toast, *_meter; NSTimer *_timer; NSMutableDictionary<NSNumber *, UILabel *> *_valLabels; UIButton *_bPreset;
}
- (UIStatusBarStyle)preferredStatusBarStyle { return UIStatusBarStyleLightContent; }

- (void)viewDidLoad {
    [super viewDidLoad];
    self.view.backgroundColor = DSHex(kBG);
    self.overrideUserInterfaceStyle = UIUserInterfaceStyleDark;
    _valLabels = [NSMutableDictionary new];
    UILayoutGuide *g = self.view.safeAreaLayoutGuide;
    UILabel *title = [UILabel new]; title.text = @"AUDIO PRO 🎚  تأخير أقل + معالجة صوت";
    title.textColor = DSHex(kCyan); title.font = DSMono(15, UIFontWeightHeavy); DSGlow(title.layer, DSHex(kCyan), 6);
    title.adjustsFontSizeToFitWidth = YES; title.minimumScaleFactor = 0.6;
    UIButton *close = [UIButton buttonWithType:UIButtonTypeSystem];
    [close setTitle:@"✕ رجوع" forState:UIControlStateNormal]; close.tintColor = DSHex(kRed);
    close.titleLabel.font = [UIFont systemFontOfSize:13 weight:UIFontWeightHeavy];
    [close addTarget:self action:@selector(closeTap) forControlEvents:UIControlEventTouchUpInside];
    UIStackView *head = [[UIStackView alloc] initWithArrangedSubviews:@[title, [UIView new], close]];
    head.alignment = UIStackViewAlignmentCenter; head.translatesAutoresizingMaskIntoConstraints = NO;
    [self.view addSubview:head];
    UIScrollView *sv = [UIScrollView new]; sv.translatesAutoresizingMaskIntoConstraints = NO;
    sv.alwaysBounceVertical = YES; sv.showsVerticalScrollIndicator = NO;
    [self.view addSubview:sv];
    _main = [UIStackView new]; _main.axis = UILayoutConstraintAxisVertical; _main.spacing = 10; _main.translatesAutoresizingMaskIntoConstraints = NO;
    [sv addSubview:_main];
    [NSLayoutConstraint activateConstraints:@[
        [head.topAnchor constraintEqualToAnchor:g.topAnchor constant:8],
        [head.leadingAnchor constraintEqualToAnchor:g.leadingAnchor constant:14], [head.trailingAnchor constraintEqualToAnchor:g.trailingAnchor constant:-14],
        [sv.topAnchor constraintEqualToAnchor:head.bottomAnchor constant:6], [sv.bottomAnchor constraintEqualToAnchor:g.bottomAnchor],
        [sv.leadingAnchor constraintEqualToAnchor:g.leadingAnchor], [sv.trailingAnchor constraintEqualToAnchor:g.trailingAnchor],
        [_main.topAnchor constraintEqualToAnchor:sv.contentLayoutGuide.topAnchor constant:6],
        [_main.bottomAnchor constraintEqualToAnchor:sv.contentLayoutGuide.bottomAnchor constant:-16],
        [_main.leadingAnchor constraintEqualToAnchor:sv.frameLayoutGuide.leadingAnchor constant:14],
        [_main.trailingAnchor constraintEqualToAnchor:sv.frameLayoutGuide.trailingAnchor constant:-14]]];
    _toast = [UILabel new]; _toast.backgroundColor = DSHex(kPanel); _toast.textColor = DSHex(kCyan); _toast.textAlignment = NSTextAlignmentCenter;
    _toast.font = DSMono(12, UIFontWeightBold); _toast.layer.cornerRadius = 10; _toast.layer.borderWidth = 1; _toast.layer.borderColor = DSHex(kCyan).CGColor;
    _toast.clipsToBounds = YES; _toast.alpha = 0; _toast.numberOfLines = 3;
    _toast.translatesAutoresizingMaskIntoConstraints = NO; [self.view addSubview:_toast];
    [NSLayoutConstraint activateConstraints:@[
        [_toast.centerXAnchor constraintEqualToAnchor:self.view.centerXAnchor], [_toast.bottomAnchor constraintEqualToAnchor:g.bottomAnchor constant:-24],
        [_toast.widthAnchor constraintLessThanOrEqualToAnchor:self.view.widthAnchor constant:-40], [_toast.widthAnchor constraintGreaterThanOrEqualToConstant:200],
        [_toast.heightAnchor constraintGreaterThanOrEqualToConstant:38]]];
    [self rebuild];
}
- (void)viewDidAppear:(BOOL)animated {
    [super viewDidAppear:animated];
    [_timer invalidate];
    _timer = [NSTimer scheduledTimerWithTimeInterval:1.0 target:self selector:@selector(tick) userInfo:nil repeats:YES];
    [self tick];
}
- (void)viewWillDisappear:(BOOL)animated { [super viewWillDisappear:animated]; [_timer invalidate]; _timer = nil; }
- (void)dealloc { [_timer invalidate]; }
- (void)tick { _meter.text = DSAPMeterText(); }
- (void)closeTap { [self dismissViewControllerAnimated:YES completion:nil]; }
- (void)toast:(NSString *)t {
    _toast.text = [NSString stringWithFormat:@"  %@  ", t];
    [_toast.layer removeAllAnimations];
    [UIView animateWithDuration:0.2 animations:^{ self->_toast.alpha = 1; } completion:^(BOOL f) {
        [UIView animateWithDuration:0.3 delay:2.4 options:0 animations:^{ self->_toast.alpha = 0; } completion:nil];
    }];
}

- (UIView *)sliderRow:(int)tag min:(float)mn max:(float)mx value:(float)v color:(UIColor *)c {
    UILabel *lab = [UILabel new]; lab.font = [UIFont systemFontOfSize:11.5 weight:UIFontWeightHeavy]; lab.textColor = DSHex(kText);
    lab.text = DSAPSliderText(tag, v); _valLabels[@(tag)] = lab;
    UISlider *s = [UISlider new]; s.minimumValue = mn; s.maximumValue = mx; s.value = v; s.tag = tag; s.tintColor = c;
    [s addTarget:self action:@selector(sliderChanged:) forControlEvents:UIControlEventValueChanged];
    UIStackView *r = [[UIStackView alloc] initWithArrangedSubviews:@[lab, s]]; r.axis = UILayoutConstraintAxisVertical; r.spacing = 2;
    return r;
}

- (void)rebuild {
    for (UIView *v in [_main.arrangedSubviews copy]) { [_main removeArrangedSubview:v]; [v removeFromSuperview]; }
    [_valLabels removeAllObjects];
    UIColor *cy = DSHex(kCyan), *gr = DSHex(kGreen), *off = DSHex(kDim), *pu = DSHex(kPurple);
    // ---------- تقليل التأخير
    UIButton *bAg = DSUBtn(self, DSAgoraLowLatTitle(), @"bolt.fill", DSAgoraLowLatIsOn() ? gr : off, @selector(agoraTap:));
    UIButton *bBuf = DSUBtn(self, DSAudioBufTitle(), @"waveform", DSAudioBufIsOn() ? gr : off, @selector(bufTap:));
    UIButton *bQ = DSUBtn(self, DSAudioQoSTitle(), @"antenna.radiowaves.left.and.right", DSAudioQoSIsOn() ? gr : off, @selector(qosTap:));
    UIButton *bUl = DSUBtn(self, DSUltraTitle(), @"bolt.horizontal.circle.fill", DSUltraIsOn() ? gr : off, @selector(ultraModeTap:));
    UIButton *bSr = DSUBtn(self, DSAPSR48() ? @"مطابقة 48kHz: ON" : @"مطابقة 48kHz: OFF", @"metronome", DSAPSR48() ? gr : off, @selector(srTap:));
    UIButton *bCap = DSUBtn(self, DSAPNetCapTitle(), @"gauge.with.dots.needle.33percent", DSAPNetCap() > 0 ? gr : off, @selector(capTap:));
    _meter = DSULabel(DSAPMeterText(), DSHex(kText)); _meter.font = DSMono(11, UIFontWeightMedium);
    UILabel *inf1 = DSULabel(@"الأزرار الأربعة الأولى هي نفسها بالقائمة الرئيسية وقائمة ULTRA (تتزامن معها). مطابقة 48kHz: تطلب من النظام تردد 48 ألف حتى لا يعيد تحويل الصوت. سقف الشبكة: يحدد أقصى مخزن لصوت الروم (أصغر = أسرع لكن تقطيع أكثر إذا النت ضعيف). الأرقام أعلاه من iOS نفسه وتُحدَّث كل ثانية. تأخير الشبكة بين المتكلم وجهازك ما يمكن إلغاؤه.", DSHex(kDim));
    [_main addArrangedSubview:DSUCard(@"تقليل التأخير", cy, @[DSURow(@[bAg, bBuf]), DSURow(@[bQ, bUl]), DSURow(@[bSr, bCap]), _meter, inf1])];
    // ---------- معالجة الصوت
    BOOL on = gAP.on != 0;
    UIButton *bOn = DSUBtn(self, on ? @"معالجة الصوت: ON" : @"معالجة الصوت: OFF", @"slider.vertical.3", on ? gr : off, @selector(apOnTap:));
    _bPreset = DSUBtn(self, [NSString stringWithFormat:@"النمط: %@", DSAPPreNames()[DSAPPreset()]], @"wand.and.stars", pu, @selector(presetTap:));
    UIView *s1 = [self sliderRow:1 min:-12 max:12 value:gAP.bass color:pu];
    UIView *s2 = [self sliderRow:2 min:-12 max:12 value:gAP.mid color:pu];
    UIView *s3 = [self sliderRow:3 min:-12 max:12 value:gAP.treb color:pu];
    UIView *s4 = [self sliderRow:4 min:0 max:100 value:gAP.comp * 100.0f color:pu];
    UIView *s5 = [self sliderRow:5 min:-65 max:-30 value:(gAP.gate < -1.0f ? gAP.gate : -65.0f) color:pu];
    UIButton *bHp = DSUBtn(self, gAP.hpf ? @"قطع الدندنة 80Hz: ON" : @"قطع الدندنة 80Hz: OFF", @"waveform.path", gAP.hpf ? gr : off, @selector(hpfTap:));
    UIButton *bMo = DSUBtn(self, gAP.mono ? @"أحادي: ON" : @"أحادي: OFF", @"speaker.fill", gAP.mono ? gr : off, @selector(monoTap:));
    UIButton *bRs = DSUBtn(self, @"إعادة ضبط المعالجة", @"arrow.counterclockwise", DSHex(kAmber), @selector(resetTap:));
    UILabel *inf2 = DSULabel(@"تعمل على مخرج الصوت النهائي (كل ما يمر عبر AudioUnit) وتضيف ~0ms لأنها بلا مخزن ولا look-ahead. موازنة الأصوات: ترفع الهادئ وتخفض العالي حتى ما يتفاوت المتكلمون. بوابة الضوضاء: تخفض الهمس بين الكلمات وتبقى مفتوحة 150ms بعد الكلام. تُحفظ الإعدادات وتُحمَّل عند فتح اللعبة. تعدّل صوتك أنت كمستمع فقط. لا تشتغل إذا المحرك يمرر الصوت خارج AudioUnit.", DSHex(kDim));
    [_main addArrangedSubview:DSUCard(@"معالجة الصوت", pu, @[DSURow(@[bOn, _bPreset]), s1, s2, s3, s4, s5, DSURow(@[bHp, bMo]), DSURow(@[bRs]), inf2])];
}

- (void)agoraTap:(UIButton *)b { DSAgoraLowLatCycle(); [self rebuild]; [self toast:@"يُطبَّق على روم الصوت الحالي — إذا ما حسّيت فرق اخرج وادخل الروم"]; }
- (void)bufTap:(UIButton *)b { DSAudioBufCycle(); [self rebuild]; [self toast:@"النظام يقرّب لأقرب قيمة يدعمها الجهاز"]; }
- (void)qosTap:(UIButton *)b { DSAudioQoSToggle(); [self rebuild]; }
- (void)ultraModeTap:(UIButton *)b { DSUltraModeCycle(); [self rebuild]; [self toast:[NSString stringWithFormat:@"Ultra: %@", DSUltraModeName(DSUltraMode())]]; }
- (void)srTap:(UIButton *)b {
    [DSAPD() setBool:!DSAPSR48() forKey:@"DSAPSR48"];
    DSAPApplySession(); [self rebuild];
    [self toast:(DSAPSR48() ? @"طلب تردد 48kHz من النظام" : @"أُلغي الطلب — يرجع لتردد اللعبة بعد إعادة فتحها")];
}
- (void)capTap:(UIButton *)b {
    [DSAPD() setInteger:(DSAPNetCap() + 1) % 5 forKey:@"DSAPNetCap"];
    DSAPApplyAgora(gDSLastEngine);   // لو ما في محرك بعد، يُطبَّق أول ما ينشأ
    [self rebuild];
    [self toast:(DSAPNetCap() ? @"قيم صغيرة = تأخير أقل لكن تقطيع أكثر. إذا انقطع الصوت ارفعها أو OFF ثم أعد دخول الروم" : @"OFF — للرجوع الكامل اخرج وادخل الروم")];
}
- (void)apOnTap:(UIButton *)b { gAP.on = !gAP.on; gAP.gen++; DSAPSave(); [self rebuild]; [self toast:(gAP.on ? @"المعالجة مفعّلة على صوت اللعبة" : @"المعالجة متوقفة")]; }
- (void)presetTap:(UIButton *)b {
    DSAPSetPreset((DSAPPreset() + 1) % DS_AP_PRE_N);
    if (!gAP.on) { gAP.on = 1; DSAPSave(); }
    [self rebuild];
}
- (void)hpfTap:(UIButton *)b { gAP.hpf = !gAP.hpf; gAP.gen++; [DSAPD() setInteger:0 forKey:@"DSAPPreset"]; DSAPSave(); [self rebuild]; }
- (void)monoTap:(UIButton *)b { gAP.mono = !gAP.mono; gAP.gen++; DSAPSave(); [self rebuild]; }
- (void)resetTap:(UIButton *)b {
    gAP.bass = gAP.mid = gAP.treb = 0; gAP.comp = 0; gAP.gate = 0; gAP.hpf = 0; gAP.mono = 0; gAP.gen++;
    [DSAPD() setInteger:0 forKey:@"DSAPPreset"]; DSAPSave(); [self rebuild]; [self toast:@"أُعيد ضبط المعالجة"];
}
- (void)sliderChanged:(UISlider *)s {
    int t = (int)s.tag; float v = s.value;
    if (t == 1) gAP.bass = roundf(v); else if (t == 2) gAP.mid = roundf(v); else if (t == 3) gAP.treb = roundf(v);
    else if (t == 4) gAP.comp = v / 100.0f; else gAP.gate = (v <= -64.0f) ? 0.0f : roundf(v);
    gAP.gen++; [DSAPD() setInteger:0 forKey:@"DSAPPreset"]; DSAPSave();
    _valLabels[@(t)].text = DSAPSliderText(t, v);
    [_bPreset setTitle:[NSString stringWithFormat:@"النمط: %@", DSAPPreNames()[0]] forState:UIControlStateNormal];
}
@end

static void DSAgoraApplyParams(id engine) {
    if (!engine) return;
    gDSLastEngine = engine;
    gDSKeyOK = 0; gDSKeyAll = 0;
    DSAgoraApplyLowLatency(engine, DSAgoraLowLat());
    DSAudioApplyAgoraGain(engine);   // تقوية الصوت (Agora الرسمي)
    DSAudioApplyAgoraAdv(engine);    // Agora المتقدم
    DSUltraApplyAgora(engine);       // Ultra
    DSAPApplyAgora(engine);          // AUDIO PRO: سقف تأخير الشبكة (إن اخترته يغلب على Ultra)
    // ملف حر: Documents/AflatoonSuite/agora_params.json  مثال:  {"che.audio.neteq.fast_accelerate": true}
    NSString *path = [DSDir() stringByAppendingPathComponent:@"agora_params.json"];
    if (![[NSFileManager defaultManager] fileExistsAtPath:path]) { [@"{}" writeToFile:path atomically:YES encoding:NSUTF8StringEncoding error:nil]; return; }
    NSData *d = [NSData dataWithContentsOfFile:path];
    id obj = d.length ? [NSJSONSerialization JSONObjectWithData:d options:0 error:nil] : nil;
    if (![obj isKindOfClass:NSDictionary.class]) return;
    for (NSString *k in (NSDictionary *)obj) {     // كل مفتاح لحاله: مفتاح خاطئ ما يوقف الباقي
        NSData *one = [NSJSONSerialization dataWithJSONObject:@{ k: ((NSDictionary *)obj)[k] } options:0 error:nil];
        NSString *js = one ? [[NSString alloc] initWithData:one encoding:NSUTF8StringEncoding] : nil;
        DSAgoraSetParameters(engine, js);
        NSLog(@"[AflatoonSuite] Agora param: %@", js);
    }
}

static void DSAgoraLowLatCycle(void) {
    NSInteger next = (DSAgoraLowLat() + 1) % 6;
    [NSUserDefaults.standardUserDefaults setInteger:next forKey:@"DSAgoraLowLat"];
    if (next >= 5) DSZegoApplyConfig();
    DSAgoraApplyParams(gDSLastEngine);   // لو ما في محرك بعد، يُطبَّق أول ما ينشأ
}

static void DSEnsureVoiceSpeedWired(id engine) {   // يستدعى عند أول انضمام ناجح لروم
    if (!engine) return;
    static __weak id wiredEngine; if (wiredEngine == engine) return; wiredEngine = engine;   // لكل محرك: يُعاد الربط لو أُنشئ محرك جديد
    DSAgoraApplyParams(engine);   // تقليل التأخير + agora_params.json
    @try {
        if (!gDSAudioProxy) gDSAudioProxy = [DSAudioFrameProxy new];
        if ([engine respondsToSelector:@selector(setAgoraAudioFrameDelegate:)])
            [engine performSelector:@selector(setAgoraAudioFrameDelegate:) withObject:gDSAudioProxy];
        // تفعيل استلام الصوت الخام قبل الخلط، وضع قراءة وكتابة (2)، عيّنات 10ms عند 48kHz
        SEL sel = NSSelectorFromString(@"setPlaybackAudioFrameParametersWithSampleRate:channel:mode:samplesPerCall:");
        if ([engine respondsToSelector:sel]) {
            NSMethodSignature *sig = [engine methodSignatureForSelector:sel];
            NSInvocation *inv = [NSInvocation invocationWithMethodSignature:sig];
            inv.selector = sel; inv.target = engine;
            NSInteger sr = 48000, ch = 1, mode = 2, spc = 480;
            [inv setArgument:&sr atIndex:2]; [inv setArgument:&ch atIndex:3];
            [inv setArgument:&mode atIndex:4]; [inv setArgument:&spc atIndex:5];
            [inv invoke];
        }
    } @catch (__unused NSException *e) {}
}

#pragma mark - صوت دخول الروم (ملف محلي فقط، بدون أي تسجيل أو سمع لأحد)

// ضع ملف الصوت باسم join.mp3 أو join.wav أو join.m4a أو join.caf داخل:
// Documents/AflatoonSuite  (نفس مجلد settings.json — يظهر عبر File Sharing في ESign/Files)
static AVAudioPlayer *gJoinPlayer;

static NSString *DSFindJoinSoundFile(void) {
    NSArray *names = @[@"join.mp3", @"join.wav", @"join.m4a", @"join.caf"];
    for (NSString *n in names) {
        NSString *p = [DSDir() stringByAppendingPathComponent:n];
        if ([[NSFileManager defaultManager] fileExistsAtPath:p]) return p;
    }
    return nil;
}

static void DSPlayJoinSound(void) {
    if (![DSSettings shared].joinSoundOn) return;
    NSString *path = DSFindJoinSoundFile();
    if (!path) { NSLog(@"[AflatoonSuite] join sound: ضع ملف join.mp3/.wav/.m4a/.caf داخل Documents/AflatoonSuite"); return; }
    dispatch_async(dispatch_get_main_queue(), ^{
        NSError *err = nil;
        [[AVAudioSession sharedInstance] setCategory:AVAudioSessionCategoryAmbient error:nil];   // صيغة كلاسيكية، متوفرة بكل إصدارات SDK
        [[AVAudioSession sharedInstance] setActive:YES error:nil];
        AVAudioPlayer *p = [[AVAudioPlayer alloc] initWithContentsOfURL:[NSURL fileURLWithPath:path] error:&err];
        if (!p) { NSLog(@"[AflatoonSuite] تعذر تشغيل ملف الصوت: %@", err); return; }
        p.enableRate = YES;
        float r = [DSSettings shared].joinSoundRate; if (r < 1) r = 1; if (r > 4) r = 4;
        p.rate = r;
        p.volume = 1.0;
        gJoinPlayer = p;   // تمسكه حتى ما ينقطع بالـ ARC قبل ما يخلّص
        [p play];
    });
}

// ── بديل مدمج لـ MSHookMessageEx ──────────────────────────────────────────────
// كود Logos المولَّد يستدعي MSHookMessageEx من CydiaSubstrate، وهذا كان يجعل الـ dylib
// يعتمد على Substrate (ويفشل الحقن بدون جيلبريك). نعرّف الدالة هنا بنفس التوقيع
// باستخدام ObjC runtime فقط، فيُحَلّ الرمز محلياً ويسقط الاعتماد على Substrate.
#ifdef __cplusplus
extern "C" {
#endif
void MSHookMessageEx(Class cls, SEL sel, IMP imp, IMP *result);
#ifdef __cplusplus
}
#endif

void MSHookMessageEx(Class cls, SEL sel, IMP imp, IMP *result) {
    if (result) *result = NULL;
    if (!cls || !sel || !imp) return;
    Method m = class_getInstanceMethod(cls, sel);   // للـ class methods يمرّر Logos الـ metaclass
    if (!m) return;                                 // الدالة غير موجودة في هذا الإصدار من المكتبة
    const char *types = method_getTypeEncoding(m);
    IMP old = NULL;
    if (class_addMethod(cls, sel, imp, types)) {
        old = method_getImplementation(m);          // كانت موروثة: الأصل هو دالة الأب
    } else {
        old = method_setImplementation(m, imp);     // الكلاس يملكها: نستبدلها ونحفظ الأصل
    }
    if (result) *result = old;
}

// Hook مكتبة Agora (إن وجدت بالتطبيق) — يشتغل الصوت فقط عند نجاح الانضمام الفعلي للروم،
// ولا يتدخّل بأي صوت ثاني داخل المكالمة ولا يسمع/يسجّل أحد — تشغيل ملف محلي فقط.
%group DSAgoraJoinSoundHooks

// تم تأكيد أسماء الدوال هذه من ثنائيات AgoraRtcKit.framework الفعلية داخل IPA اللعبة.
// غرف يلا لودو تستخدم أسلوب القنوات المتعددة (AgoraRtcChannel عبر createRtcChannel:)،
// فالانضمام الفعلي للروم الصوتي يصير على كائن القناة، لا على AgoraRtcEngineKit نفسه.

%hook AgoraRtcChannel

- (int)joinChannelByToken:(NSString *)token info:(NSString *)info uid:(NSUInteger)uid options:(id)options joinSuccess:(void (^)(NSString *, NSUInteger, NSInteger))joinSuccessBlock {
    int r = %orig;
    if (r == 0) DSPlayJoinSound();
    return r;
}

- (int)joinChannelByToken:(NSString *)token info:(NSString *)info uid:(NSUInteger)uid options:(id)options {
    int r = %orig;
    if (r == 0) DSPlayJoinSound();
    return r;
}

- (int)joinChannelByUserAccount:(NSString *)userAccount token:(NSString *)token options:(id)options {
    int r = %orig;
    if (r == 0) DSPlayJoinSound();
    return r;
}

%end

// احتياطي: إذا روم معيّن استخدم أسلوب القناة الواحدة (الانضمام مباشرة على المحرك)
%hook AgoraRtcEngineKit

+ (instancetype)sharedEngineWithAppId:(NSString *)appId delegate:(id)delegate {
    id r = %orig;
    DSEnsureVoiceSpeedWired(r);
    return r;
}
+ (instancetype)sharedEngineWithAppId:(NSString *)appId error:(id)err {
    id r = %orig;
    DSEnsureVoiceSpeedWired(r);
    return r;
}
+ (instancetype)sharedEngineWithAppId:(NSString *)appId extensionDelegate:(id)delegate {
    id r = %orig;
    DSEnsureVoiceSpeedWired(r);
    return r;
}
+ (instancetype)sharedEngineWithConfig:(id)config extensionDelegate:(id)delegate {
    id r = %orig;
    DSEnsureVoiceSpeedWired(r);
    return r;
}
- (id)createRtcChannel:(NSString *)channelId {   // غرف يلا لودو: نربط المراقب عند إنشاء القناة أيضاً
    if (gForceZegoOnly) return nil;   // نمنع حتى إنشاء كائن القناة نفسه
    id r = %orig;
    DSEnsureVoiceSpeedWired(self);
    return r;
}
+ (instancetype)sharedEngineWithConfig:(id)config delegate:(id)delegate {
    id r = %orig;
    DSEnsureVoiceSpeedWired(r);
    return r;
}

- (int)joinChannelByToken:(NSString *)token channelId:(NSString *)channelId info:(NSString *)info uid:(NSUInteger)uid joinSuccess:(void (^)(NSString *, NSUInteger, NSInteger))joinSuccessBlock {
    if (gForceZegoOnly) return -2;   // ERR_INVALID_ARGUMENT: نمنع Agora من الانضمام أصلاً حتى يضطر مسار اللعبة البديل (Zego) للعمل
    int r = %orig;
    if (r == 0) DSPlayJoinSound();
    return r;
}

- (int)joinChannelByToken:(NSString *)token channelId:(NSString *)channelId info:(NSString *)info uid:(NSUInteger)uid options:(id)options joinSuccess:(void (^)(NSString *, NSUInteger, NSInteger))joinSuccessBlock {
    if (gForceZegoOnly) return -2;
    int r = %orig;
    if (r == 0) DSPlayJoinSound();
    return r;
}

%end
%end

#pragma mark - الكيبورد: تكرار الأرقام + تفكيك الحروف

// يعمل على أي UITextField / UITextView داخل التطبيق المضيف (بما فيها كيبورد Unity)
// عبر اعتراض insertText: و deleteBackward. لا يمسّ شاشات الأداة نفسها ولا حقول كلمة السر.
static BOOL gKbBusy = NO;   // حارس إعادة الدخول (الخيط الرئيسي فقط)

static inline BOOL DSKbIsDigit(unichar c) {
    return (c >= '0' && c <= '9') || (c >= 0x0660 && c <= 0x0669) || (c >= 0x06F0 && c <= 0x06F9);
}
static BOOL DSKbAllDigits(NSString *s) {
    if (!s.length) return NO;
    for (NSUInteger i = 0; i < s.length; i++) if (!DSKbIsDigit([s characterAtIndex:i])) return NO;
    return YES;
}
static BOOL DSKbIsLetter(NSString *cluster) {
    if (!cluster.length) return NO;
    return [NSCharacterSet.letterCharacterSet characterIsMember:[cluster characterAtIndex:0]];
}
static BOOL DSKbIsMark(NSString *cluster) {
    if (!cluster.length) return NO;
    return [NSCharacterSet.nonBaseCharacterSet characterIsMember:[cluster characterAtIndex:0]];
}

// النص قبل المؤشر (آخر n حرف)
static NSString *DSKbBefore(id<UITextInput> t, NSInteger n) {
    UITextRange *sel = t.selectedTextRange; if (!sel) return @"";
    UITextPosition *end = sel.start, *start = [t positionFromPosition:end offset:-n];
    if (!start) start = t.beginningOfDocument;
    UITextRange *r = [t textRangeFromPosition:start toPosition:end];
    return r ? ([t textInRange:r] ?: @"") : @"";
}

// هل النص ينتهي بنمط  D.D  (نفس الرقم مكرراً)؟ يرجع D
static NSString *DSKbTrailingRun(NSString *before) {
    NSUInteger n = before.length, i = n;
    while (i > 0 && DSKbIsDigit([before characterAtIndex:i - 1])) i--;
    NSUInteger n2 = n - i;
    if (!n2 || i < n2 + 1) return nil;
    if ([before characterAtIndex:i - 1] != '.') return nil;
    NSString *d2 = [before substringFromIndex:i];
    NSString *d1 = [before substringWithRange:NSMakeRange(i - 1 - n2, n2)];
    return [d1 isEqualToString:d2] ? d2 : nil;
}

// الحقل مؤهل للتعديل؟ (ليس من شاشات الأداة، ليس كلمة سر، تحديد فارغ، لا كتابة IME معلّقة)
static inline BOOL DSIsMiniWin(UIWindow *w) { return w && [NSStringFromClass(w.class) isEqualToString:@"DSMiniWindow"]; }

static BOOL DSKbPlanInsertX(id t, NSString *text, NSUInteger *del, NSString **rep);   // أوضاع الكيبورد الجديدة (تحت)
static BOOL DSKbPlanDeleteX(id t, NSUInteger *del, NSString **rep);

static BOOL DSKbEligible(id t) {
    if (gKbBusy || (!gKbRepeat && !gKbSplit && !DSKbXActive()) || ![NSThread isMainThread]) return NO;
    if (![t isKindOfClass:UIView.class]) return NO;
    if ([((UIView *)t).window isKindOfClass:DSPassWindow.class] || DSIsMiniWin(((UIView *)t).window)) return NO;
    if ([(id<UITextInputTraits>)t isSecureTextEntry]) return NO;
    UITextRange *sel = [(id<UITextInput>)t selectedTextRange];
    if (!sel || !sel.isEmpty) return NO;
    if ([(id<UITextInput>)t markedTextRange]) return NO;
    return YES;
}

// خطة الإدخال: احذف `del` حرفاً قبل المؤشر ثم أدخل `rep`
static BOOL DSKbPlanInsert(id t, NSString *text, NSUInteger *del, NSString **rep) {
    if (!text.length || !DSKbEligible(t)) return NO;
    if (DSKbXActive() && DSKbPlanInsertX(t, text, del, rep)) return YES;   // أرقام/عكس/أسماء (الجديدة) أولاً
    // 1) تكرار الأرقام: 1 → 1.1 ، ثم 3 → 13.13 ، ثم 5 → 135.135
    if (gKbRepeat && DSKbAllDigits(text)) {
        NSString *run = DSKbTrailingRun(DSKbBefore(t, 200));
        NSString *raw = [(run ?: @"") stringByAppendingString:text];
        *del = run ? run.length * 2 + 1 : 0;
        *rep = [NSString stringWithFormat:@"%@.%@", raw, raw];
        return YES;
    }
    // 2) تفكيك الحروف: بين كل حرفين مسافة
    if (gKbSplit) {
        __block BOOL hasLetter = NO;
        [text enumerateSubstringsInRange:NSMakeRange(0, text.length) options:NSStringEnumerationByComposedCharacterSequences
            usingBlock:^(NSString *c, NSRange r, NSRange er, BOOL *stop) { if (DSKbIsLetter(c)) { hasLetter = YES; *stop = YES; } }];
        if (!hasLetter) return NO;
        NSString *before = DSKbBefore(t, 4);
        NSString *prev = nil;
        if (before.length) {
            NSRange lr = [before rangeOfComposedCharacterSequenceAtIndex:before.length - 1];
            prev = [before substringWithRange:lr];
        }
        __block BOOL prevLetterish = prev && (DSKbIsLetter(prev) || DSKbIsMark(prev));
        NSMutableString *out = [NSMutableString string];
        [text enumerateSubstringsInRange:NSMakeRange(0, text.length) options:NSStringEnumerationByComposedCharacterSequences
            usingBlock:^(NSString *c, NSRange r, NSRange er, BOOL *stop) {
            BOOL letter = DSKbIsLetter(c);
            if (letter && prevLetterish) [out appendString:@" "];
            [out appendString:c];
            prevLetterish = letter || DSKbIsMark(c);
        }];
        if ([out isEqualToString:text]) return NO;
        *del = 0; *rep = out;
        return YES;
    }
    return NO;
}

// خطة الحذف: مسح 135.135 يرجع 13.13 (حذف رقم واحد من الأصل)، ومسح حرف مفكّك يمسح مسافته أيضاً
static BOOL DSKbPlanDelete(id t, NSUInteger *del, NSString **rep) {
    if (!DSKbEligible(t)) return NO;
    if (DSKbXActive() && DSKbPlanDeleteX(t, del, rep)) return YES;
    NSString *before = DSKbBefore(t, 200);
    if (gKbRepeat) {
        NSString *run = DSKbTrailingRun(before);
        if (run) {
            *del = run.length * 2 + 1;
            if (run.length > 1) { NSString *r2 = [run substringToIndex:run.length - 1]; *rep = [NSString stringWithFormat:@"%@.%@", r2, r2]; }
            else *rep = nil;
            return YES;
        }
    }
    if (gKbSplit && before.length >= 3) {
        NSUInteger n = before.length;
        NSString *l2 = [before substringWithRange:NSMakeRange(n - 1, 1)], *l1 = [before substringWithRange:NSMakeRange(n - 3, 1)];
        if ([before characterAtIndex:n - 2] == ' ' && DSKbIsLetter(l2) && DSKbIsLetter(l1)) { *del = 2; *rep = nil; return YES; }
    }
    return NO;
}

#pragma mark - أوضاع الكيبورد الجديدة: أرقام (ترتيب / تدبيل / تدبيل الأخير) · عكس الرسالة · أسماء بحرف
// تُبنى الرسالة «منطقياً» (forward) ثم تُكتب بالحقل كما هي أو معكوسة (هلو ← وله)، فيعمل العكس مع أي وضع.
// أوضاع الأرقام (تجمع كل أرقامك المتصلة بمجموعات من 3 من اليسار):
//   1 ترتيب:  938747 → 938 747      2 تدبيل: 929818 → 929 929 818 818      3 تدبيل الأخير: 938100 → 938 100 100
static int DSNumPutGroup(unichar *out, int o, int cap, const unichar *g, int gl, BOOL space) {
    if (space && o < cap) out[o++] = ' ';
    for (int i = 0; i < gl && o < cap; i++) out[o++] = g[i];
    return o;
}
static int DSNumRender(int mode, const unichar *raw, int n, unichar *out, int cap) {
    int o = 0;
    for (int i = 0; i < n; i += 3) {
        int gl = (n - i < 3) ? n - i : 3, reps = (mode == 2) ? 2 : 1;
        for (int r = 0; r < reps; r++) o = DSNumPutGroup(out, o, cap, raw + i, gl, o > 0);
    }
    if (mode == 3 && n > 0) { int last = ((n - 1) / 3) * 3; o = DSNumPutGroup(out, o, cap, raw + last, n - last, YES); }
    return o;
}
// يستخرج الأرقام الخام من مقطع منسَّق بهذا النمط. -1 = المقطع ليس بصيغة النمط حرفياً (فنبدأ رقماً جديداً)
static int DSNumParse(int mode, const unichar *run, int n, unichar *raw) {
    int ts[64], tl[64], k = 0, i = 0;
    while (i < n) {
        if (!DSKbIsDigit(run[i])) return -1;
        int st = i; while (i < n && DSKbIsDigit(run[i])) i++;
        if (k >= 64) return -1;
        ts[k] = st; tl[k] = i - st; k++;
        if (i < n) { if (run[i] != ' ' || i + 1 >= n) return -1; i++; }
    }
    if (k == 0) return -1;
    int use = k, step = 1;
    if (mode == 2) { if (k % 2) return -1; step = 2; }
    if (mode == 3) { if (k < 2) return -1; use = k - 1; }
    int r = 0;
    for (int t = 0; t < use; t += step) for (int j = 0; j < tl[t]; j++) raw[r++] = run[ts[t] + j];
    unichar chk[256]; int cl = DSNumRender(mode, raw, r, chk, 256);
    if (cl != n || memcmp(chk, run, (size_t)n * sizeof(unichar)) != 0) return -1;
    return r;
}
// آخر مقطع «أرقام ومسافات» ينتهي به النص (يبدأ برقم). NSNotFound إن لم يوجد
static NSRange DSKbNumRun(NSString *s) {
    NSUInteger n = s.length, i = n;
    while (i > 0) { unichar c = [s characterAtIndex:i - 1]; if (DSKbIsDigit(c) || c == ' ') i--; else break; }
    while (i < n && [s characterAtIndex:i] == ' ') i++;
    if (i >= n) return NSMakeRange(NSNotFound, 0);
    return NSMakeRange(i, n - i);
}

// ---- أسماء بحرف (بيانات من ssl_kalimat.json: كل حرف ← اسم واحد لكل فئة) ----
static const char kKalimatJSON[] = "{\"ا\":{\"جماد\":\"إبريق\",\"ولد\":\"أحمد\",\"بنت\":\"آمنة\",\"دولة\":\"أستراليا\",\"حيوان\":\"أسد\",\"نبات\":\"أرز\"},\"ب\":{\"جماد\":\"باب\",\"ولد\":\"باسم\",\"بنت\":\"بشرى\",\"دولة\":\"بلجيكا\",\"حيوان\":\"ببغاء\",\"نبات\":\"برتقالة\"},\"ت\":{\"جماد\":\"تاج\",\"ولد\":\"تامر\",\"بنت\":\"تغريد\",\"دولة\":\"تونس\",\"حيوان\":\"تمساح\",\"نبات\":\"تفاح\"},\"ث\":{\"جماد\":\"ثوب\",\"ولد\":\"ثامر\",\"بنت\":\"ثريا\",\"دولة\":null,\"حيوان\":\"ثعلب\",\"نبات\":\"ثوم\"},\"ج\":{\"جماد\":\"جرس\",\"ولد\":\"جمال\",\"بنت\":\"جميلة\",\"دولة\":\"جيبوتي\",\"حيوان\":\"جمل\",\"نبات\":\"جزر\"},\"ح\":{\"جماد\":\"حبل\",\"ولد\":\"حسن\",\"بنت\":\"حنان\",\"دولة\":null,\"حيوان\":\"حصان\",\"نبات\":\"حناء\"},\"خ\":{\"جماد\":\"خاتم\",\"ولد\":\"خالد\",\"بنت\":\"خديجة\",\"دولة\":null,\"حيوان\":\"خروف\",\"نبات\":\"خيار\"},\"د\":{\"جماد\":\"درج\",\"ولد\":\"داود\",\"بنت\":\"دعاء\",\"دولة\":\"دومينيكا\",\"حيوان\":\"دب\",\"نبات\":\"دوار الشمس\"},\"ذ\":{\"جماد\":\"ذهب\",\"ولد\":\"ذياب\",\"بنت\":\"ذكرى\",\"دولة\":null,\"حيوان\":\"ذئب\",\"نبات\":\"ذرة\"},\"ر\":{\"جماد\":\"رمح\",\"ولد\":\"رائد\",\"بنت\":\"ريم\",\"دولة\":\"روسيا\",\"حيوان\":\"راكون\",\"نبات\":\"ريحان\"},\"ز\":{\"جماد\":\"زجاج\",\"ولد\":\"زيد\",\"بنت\":\"زينب\",\"دولة\":\"زامبيا\",\"حيوان\":\"زرافة\",\"نبات\":\"زيتون\"},\"س\":{\"جماد\":\"سرير\",\"ولد\":\"سامر\",\"بنت\":\"سارة\",\"دولة\":\"سوريا\",\"حيوان\":\"سمك\",\"نبات\":\"سدر\"},\"ش\":{\"جماد\":\"شمعة\",\"ولد\":\"شادي\",\"بنت\":\"شيماء\",\"دولة\":\"شيلي\",\"حيوان\":\"شمبانزي\",\"نبات\":\"شاي\"},\"ص\":{\"جماد\":\"صندوق\",\"ولد\":\"صالح\",\"بنت\":\"صفاء\",\"دولة\":\"صربيا\",\"حيوان\":\"صقر\",\"نبات\":\"صبار\"},\"ض\":{\"جماد\":\"ضرس\",\"ولد\":\"ضياء\",\"بنت\":\"ضحى\",\"دولة\":null,\"حيوان\":\"ضفدع\",\"نبات\":\"ضومران\"},\"ط\":{\"جماد\":\"طاولة\",\"ولد\":\"طارق\",\"بنت\":\"طيبة\",\"دولة\":null,\"حيوان\":\"طاووس\",\"نبات\":\"طماطم\"},\"ظ\":{\"جماد\":\"ظرف\",\"ولد\":\"ظافر\",\"بنت\":\"ظبية\",\"دولة\":null,\"حيوان\":\"ظبي\",\"نبات\":\"ظيان\"},\"ع\":{\"جماد\":\"علبة\",\"ولد\":\"علي\",\"بنت\":\"عائشة\",\"دولة\":\"عُمان\",\"حيوان\":\"عصفور\",\"نبات\":\"عنب\"},\"غ\":{\"جماد\":\"غسالة\",\"ولد\":\"غسان\",\"بنت\":\"غادة\",\"دولة\":\"غانا\",\"حيوان\":\"غزال\",\"نبات\":\"غار\"},\"ف\":{\"جماد\":\"فنجان\",\"ولد\":\"فهد\",\"بنت\":\"فاطمة\",\"دولة\":\"فرنسا\",\"حيوان\":\"فيل\",\"نبات\":\"فراولة\"},\"ق\":{\"جماد\":\"قلم\",\"ولد\":\"قاسم\",\"بنت\":\"قمر\",\"دولة\":\"قطر\",\"حيوان\":\"قط\",\"نبات\":\"قمح\"},\"ك\":{\"جماد\":\"كرسي\",\"ولد\":\"كريم\",\"بنت\":\"كوثر\",\"دولة\":\"كندا\",\"حيوان\":\"كلب\",\"نبات\":\"كمثرى\"},\"ل\":{\"جماد\":\"لوح\",\"ولد\":\"لؤي\",\"بنت\":\"ليلى\",\"دولة\":\"لبنان\",\"حيوان\":\"لبؤة\",\"نبات\":\"ليمون\"},\"م\":{\"جماد\":\"مفتاح\",\"ولد\":\"محمد\",\"بنت\":\"مريم\",\"دولة\":\"مصر\",\"حيوان\":\"ماعز\",\"نبات\":\"موز\"},\"ن\":{\"جماد\":\"نافذة\",\"ولد\":\"ناصر\",\"بنت\":\"نور\",\"دولة\":\"نيبال\",\"حيوان\":\"نمر\",\"نبات\":\"نخيل\"},\"هـ\":{\"جماد\":\"هاتف\",\"ولد\":\"هاني\",\"بنت\":\"هدى\",\"دولة\":\"هندوراس\",\"حيوان\":\"هدهد\",\"نبات\":\"هندباء\"},\"و\":{\"جماد\":\"ورقة\",\"ولد\":\"وليد\",\"بنت\":\"وفاء\",\"دولة\":null,\"حيوان\":\"وزة\",\"نبات\":\"ورد\"},\"ي\":{\"جماد\":\"يد\",\"ولد\":\"ياسر\",\"بنت\":\"ياسمين\",\"دولة\":\"اليمن\",\"حيوان\":\"يمامة\",\"نبات\":\"ياسمين\"}}";
static NSDictionary *DSKbKalimat(void) {
    static NSDictionary *d; static dispatch_once_t once;
    dispatch_once(&once, ^{
        id j = [NSJSONSerialization JSONObjectWithData:[NSData dataWithBytes:kKalimatJSON length:strlen(kKalimatJSON)] options:0 error:nil];
        d = [j isKindOfClass:NSDictionary.class] ? j : @{};
    });
    return d;
}
static NSString *DSKbNamesFor(NSString *typed) {
    if (!typed.length || typed.length > 2) return nil;
    if ([typed rangeOfComposedCharacterSequenceAtIndex:0].length != typed.length) return nil;   // حرف واحد فقط
    static NSDictionary *alias; static NSArray *order; static dispatch_once_t once;
    dispatch_once(&once, ^{
        alias = @{ @"أ": @"ا", @"إ": @"ا", @"آ": @"ا", @"ٱ": @"ا", @"ى": @"ي", @"ئ": @"ي", @"ؤ": @"و", @"ة": @"هـ" };
        order = @[@"ولد", @"بنت", @"حيوان", @"نبات", @"جماد", @"دولة"];
    });
    NSDictionary *d = DSKbKalimat();
    NSDictionary *row = d[typed] ?: d[alias[typed] ?: @""];
    if (![row isKindOfClass:NSDictionary.class]) return nil;
    NSMutableArray *out = [NSMutableArray array];
    for (int i = 0; i < 6; i++) {
        if (!(gKbCats & (1 << i))) continue;
        id v = row[order[i]];
        if ([v isKindOfClass:NSString.class] && [(NSString *)v length]) [out addObject:v];
    }
    return out.count ? [out componentsJoinedByString:@" "] : nil;
}

static NSString *DSKbDropLast(NSString *s) {
    if (!s.length) return s;
    return [s substringToIndex:[s rangeOfComposedCharacterSequenceAtIndex:s.length - 1].location];
}
static NSString *DSKbReverseStr(NSString *s) {
    NSMutableString *o = [NSMutableString stringWithCapacity:s.length];
    [s enumerateSubstringsInRange:NSMakeRange(0, s.length) options:NSStringEnumerationByComposedCharacterSequences | NSStringEnumerationReverse
        usingBlock:^(NSString *c, NSRange r, NSRange er, BOOL *stop) { [o appendString:c]; }];
    return o;
}
// النص بعد كتابة `typed` في آخر النص المنطقي
static NSString *DSKbXform(NSString *fwd, NSString *typed) {
    if (gKbNames && gKbCats && fwd.length == 0) { NSString *nm = DSKbNamesFor(typed); if (nm) return nm; }
    if (gKbNum > 0 && DSKbAllDigits(typed) && typed.length <= 60) {
        NSRange rr = DSKbNumRun(fwd);
        unichar raw[256]; int rn = 0; NSString *prefix = fwd;
        if (rr.location != NSNotFound && rr.length <= 120) {
            unichar run[256]; [fwd getCharacters:run range:rr];
            int n = DSNumParse(gKbNum, run, (int)rr.length, raw);
            if (n >= 0) { rn = n; prefix = [fwd substringToIndex:rr.location]; }
        }
        if (rn + (int)typed.length > 120) return [fwd stringByAppendingString:typed];
        [typed getCharacters:raw + rn range:NSMakeRange(0, typed.length)]; rn += (int)typed.length;
        unichar out[256]; int on = DSNumRender(gKbNum, raw, rn, out, 256);
        return [prefix stringByAppendingString:[NSString stringWithCharacters:out length:(NSUInteger)on]];
    }
    return [fwd stringByAppendingString:typed];
}
// النص بعد ضغط حذف واحد (يحذف رقماً خاماً واحداً من الأرقام المنسَّقة، أو حرفاً عادياً)
static NSString *DSKbXformDelete(NSString *fwd) {
    if (gKbNum > 0) {
        NSRange rr = DSKbNumRun(fwd);
        if (rr.location != NSNotFound && rr.length <= 120) {
            unichar run[256], raw[256]; [fwd getCharacters:run range:rr];
            int n = DSNumParse(gKbNum, run, (int)rr.length, raw);
            if (n >= 0) {
                NSString *prefix = [fwd substringToIndex:rr.location];
                if (n <= 1) return prefix;
                unichar out[256]; int on = DSNumRender(gKbNum, raw, n - 1, out, 256);
                return [prefix stringByAppendingString:[NSString stringWithCharacters:out length:(NSUInteger)on]];
            }
        }
    }
    return DSKbDropLast(fwd);
}

static NSString *DSKbFullText(id<UITextInput> t) {
    UITextRange *r = [t textRangeFromPosition:t.beginningOfDocument toPosition:t.endOfDocument];
    return r ? ([t textInRange:r] ?: @"") : @"";
}
static BOOL DSKbAtEnd(id<UITextInput> t) {
    UITextRange *sel = t.selectedTextRange;
    return sel && [t comparePosition:sel.end toPosition:t.endOfDocument] == NSOrderedSame;
}
// (النص الحالي → الهدف) = احذف `del` حرفاً من الآخر ثم أدرج `rep` (أقل تغيير ممكن)
static void DSKbDiffPlan(NSString *cur, NSString *target, NSUInteger *del, NSString **rep) {
    NSUInteger m = MIN(cur.length, target.length), p = 0;
    while (p < m && [cur characterAtIndex:p] == [target characterAtIndex:p]) p++;
    if (p < cur.length) p = [cur rangeOfComposedCharacterSequenceAtIndex:p].location;   // ابدأ من حدّ حرف كامل
    __block NSUInteger cnt = 0;
    NSString *tail = [cur substringFromIndex:p];
    [tail enumerateSubstringsInRange:NSMakeRange(0, tail.length) options:NSStringEnumerationByComposedCharacterSequences
        usingBlock:^(NSString *c, NSRange r, NSRange er, BOOL *stop) { cnt++; }];
    *del = cnt; *rep = [target substringFromIndex:p];
}
static BOOL DSKbPlanInsertX(id t, NSString *text, NSUInteger *del, NSString **rep) {
    if (!DSKbXActive() || !text.length || !DSKbEligible(t)) return NO;
    id<UITextInput> ti = (id<UITextInput>)t;
    if (!DSKbAtEnd(ti)) return NO;                       // المؤشر لازم يكون بآخر النص
    NSString *cur = DSKbFullText(ti); if (cur.length > 300) return NO;
    NSString *fwd = gKbRev ? DSKbReverseStr(cur) : cur;
    NSString *target = DSKbXform(fwd, text);
    if (gKbRev) target = DSKbReverseStr(target);
    if ([target isEqualToString:[cur stringByAppendingString:text]]) return NO;   // لا تغيير: مرّر الإدخال الأصلي
    DSKbDiffPlan(cur, target, del, rep);
    return YES;
}
static BOOL DSKbPlanDeleteX(id t, NSUInteger *del, NSString **rep) {
    if (!DSKbXActive() || !DSKbEligible(t)) return NO;
    id<UITextInput> ti = (id<UITextInput>)t;
    if (!DSKbAtEnd(ti)) return NO;
    NSString *cur = DSKbFullText(ti); if (!cur.length || cur.length > 300) return NO;
    NSString *fwd = gKbRev ? DSKbReverseStr(cur) : cur;
    NSString *target = DSKbXformDelete(fwd);
    if (gKbRev) target = DSKbReverseStr(target);
    if ([target isEqualToString:DSKbDropLast(cur)]) return NO;   // نفس الحذف العادي
    DSKbDiffPlan(cur, target, del, rep);
    return YES;
}

// ---- «الكتابة السريعة» + الأوضاع: يحاكي كتابة الرسالة حرفاً حرفاً بنفس خطط الكيبورد (الجديدة ثم تكرار الأرقام ثم تفكيك الحروف) ثم العكس
static BOOL DSQuickModesOn(void) {
    id v = [NSUserDefaults.standardUserDefaults objectForKey:@"DSQuickModes"];
    return v ? [v boolValue] : YES;   // مفعّل افتراضياً: لو ما فعّلت أي وضع، النص يمرّ كما هو
}
static NSString *DSQuickModesTitle(void) { return DSQuickModesOn() ? @"أوضاع الكتابة السريعة: ON" : @"أوضاع الكتابة السريعة: OFF"; }
static void DSQuickModesToggle(void) { [NSUserDefaults.standardUserDefaults setBool:!DSQuickModesOn() forKey:@"DSQuickModes"]; }

static NSString *DSKbSimType(NSString *fwd, NSString *c) {
    NSString *nf = DSKbXform(fwd, c);   // أرقام (ترتيب/تدبيل) وأسماء بحرف
    if (DSKbXActive() && ![nf isEqualToString:[fwd stringByAppendingString:c]]) return nf;
    if (gKbRepeat && DSKbAllDigits(c)) {   // تكرار الأرقام القديم: 135 ← 135.135
        NSString *run = DSKbTrailingRun(fwd);
        NSString *raw = [(run ?: @"") stringByAppendingString:c];
        NSUInteger del = run ? run.length * 2 + 1 : 0;
        return [[fwd substringToIndex:fwd.length - del] stringByAppendingFormat:@"%@.%@", raw, raw];
    }
    if (gKbSplit && DSKbIsLetter(c)) {     // تفكيك الحروف: م ح م د
        NSString *prev = fwd.length ? [fwd substringWithRange:[fwd rangeOfComposedCharacterSequenceAtIndex:fwd.length - 1]] : nil;
        BOOL prevLetterish = prev && (DSKbIsLetter(prev) || DSKbIsMark(prev));
        return [fwd stringByAppendingString:(prevLetterish ? [@" " stringByAppendingString:c] : c)];
    }
    return [fwd stringByAppendingString:c];
}
static NSString *DSComposeMessage(NSString *msg) {
    if (!msg.length || (!gKbRepeat && !gKbSplit && !DSKbXActive())) return msg;
    BOOL savedNames = gKbNames;
    if ([msg rangeOfComposedCharacterSequenceAtIndex:0].length != msg.length) gKbNames = NO;   // «أسماء بحرف» فقط لو الرسالة حرف واحد
    __block NSString *fwd = @"";
    [msg enumerateSubstringsInRange:NSMakeRange(0, msg.length) options:NSStringEnumerationByComposedCharacterSequences
        usingBlock:^(NSString *c, NSRange r, NSRange er, BOOL *stop) { fwd = DSKbSimType(fwd, c); }];
    gKbNames = savedNames;
    return gKbRev ? DSKbReverseStr(fwd) : fwd;
}

// ===== حساسية الكيبورد =====
// الفكرة: لا يرسل أبداً وأنت تلمس الكيبورد أو تكتب. أول ما ترفع يدك (وتتوقف الكتابة) يرسل الرسالة مرة واحدة.
//  • لمس الكيبورد: يُكتشف عندما يمر اللمس عبر نافذة التطبيق (كيبورد داخل اللعبة/Unity). كيبورد iOS النظامي
//    يعمل في عملية منفصلة ولا يمرّر اللمس للتطبيق، لذلك يُكمَّل بإشارة الكتابة نفسها (آخر حرف أُدخل).
//  • ذكاء AUTO (على الجهاز، بدون إنترنت): يتعلّم إيقاع كتابتك (أرقام/حروف) ويصحّح نفسه من الإرسال المبكر.
static NSUInteger gKbSenseGen = 0;       // رقم الجيل: أي لمس/كتابة جديدة يلغي الإرسال المنتظر
static BOOL gKbTouching = NO;            // إصبعك الآن على الكيبورد
static BOOL gKbDirty = NO;               // كُتب شيء جديد منذ آخر إرسال (يمنع الإرسال المتكرر)
static double gKbLastKeyT = 0, gKbAvgGap = 0;
// ذكاء AUTO (تعلّم ذاتي على الجهاز): إحصاء إيقاع كتابتك + تصحيح ذاتي من أخطاء الإرسال المبكر
static double gKbMean[2] = {0, 0}, gKbVar[2] = {0, 0};   // [0] أرقام، [1] حروف
static int gKbLastIdx = 1;
static double gKbF = 1.0;        // معامل الثقة: يكبر إذا أرسل مبكراً، ويصغر (أسرع) كلما أصاب
static double gKbSentT = 0;      // وقت آخر إرسال (لاكتشاف الإرسال المبكر)
static __weak id gKbField = nil;
static CGRect gKbFrame;                  // مكان الكيبورد على الشاشة

static void DSKbSendNow(id t) {
    if ([t isKindOfClass:UITextField.class]) {
        UITextField *f = t; id<UITextFieldDelegate> d = f.delegate;
        if ([d respondsToSelector:@selector(textFieldShouldReturn:)]) [d textFieldShouldReturn:f];
        [f sendActionsForControlEvents:UIControlEventEditingDidEndOnExit];
    } else if ([t isKindOfClass:UITextView.class]) {
        UITextView *v = t; id<UITextViewDelegate> d = v.delegate; BOOL ok = YES;
        if ([d respondsToSelector:@selector(textView:shouldChangeTextInRange:replacementText:)])
            ok = [d textView:v shouldChangeTextInRange:v.selectedRange replacementText:@"\n"];
        if (ok) { gKbBusy = YES; [v insertText:@"\n"]; gKbBusy = NO; }   // busy: حتى لا يعيد تسليح المؤقت
    }
    if (gKbKeep) {   // «إبقاء الكيبورد»: لو اللعبة سحبت التركيز بعد الإرسال نرجّعه
        __weak id wt = t;
        dispatch_after(dispatch_time(DISPATCH_TIME_NOW, 70 * NSEC_PER_MSEC), dispatch_get_main_queue(), ^{
            id st = wt;
            if ([st isKindOfClass:UIView.class] && ((UIView *)st).window && ![(UIResponder *)st isFirstResponder]) [(UIResponder *)st becomeFirstResponder];
        });
    }
}

static void DSKbResetSense(void) { gKbSenseGen++; gKbTouching = NO; gKbDirty = NO; gKbLastKeyT = 0; gKbAvgGap = 0; gKbMean[0] = gKbMean[1] = 0; gKbVar[0] = gKbVar[1] = 0; gKbF = 1.0; gKbSentT = 0; }

static BOOL DSKbSenseFieldOK(id t) {
    if (!t || ![t isKindOfClass:UIView.class]) return NO;
    if (![t isKindOfClass:UITextField.class] && ![t isKindOfClass:UITextView.class]) return NO;
    if ([((UIView *)t).window isKindOfClass:DSPassWindow.class] || DSIsMiniWin(((UIView *)t).window)) return NO;      // شاشات الأداة نفسها
    if ([(id<UITextInputTraits>)t isSecureTextEntry]) return NO;                  // كلمات السر
    return YES;
}

static double DSKbSenseDelay(void) {
    static const double fixed[] = {0, 0.05, 0.1, 0.2, 0.4};
    NSInteger m = gKbSenseMode;
    if (m > 0 && m < 5) return fixed[m];
    // ذكاء AUTO: المهلة = (متوسط فاصل ضغطاتك + 1.5 × الانحراف) × معامل التعلّم الذاتي، بين 0.05 و0.35 ثانية
    double mean = gKbMean[gKbLastIdx];
    double d = mean > 0 ? (mean + 1.5 * sqrt(MAX(0.0, gKbVar[gKbLastIdx]))) * gKbF : 0.12;
    return MAX(0.05, MIN(0.35, d));
}

static void DSKbSenseArmN(int retry) {
    if (!gKbSense) return;
    NSUInteger gen = ++gKbSenseGen;
    double d = DSKbSenseDelay();
    dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(d * NSEC_PER_SEC)), dispatch_get_main_queue(), ^{
        if (gen != gKbSenseGen || !gKbSense || gKbTouching || !gKbDirty) return;
        id f = gKbField;
        if (!DSKbSenseFieldOK(f) || ![(UIResponder *)f isFirstResponder]) return;
        if ([(id<UITextInput>)f markedTextRange]) {            // كتابة IME لم تكتمل بعد: انتظر قليلاً
            if (retry < 5) DSKbSenseArmN(retry + 1);
            return;
        }
        NSString *txt = [f isKindOfClass:UITextField.class] ? ((UITextField *)f).text : ((UITextView *)f).text;
        NSString *trim = [txt stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceAndNewlineCharacterSet];
        if (trim.length < (NSUInteger)MAX(1, gKbMinChars)) return;
        gKbDirty = NO; gKbSenseGen++;
        double sentT = DSNow(); gKbSentT = sentT;
        dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(2.0 * NSEC_PER_SEC)), dispatch_get_main_queue(), ^{
            if (gKbSentT == sentT) { gKbF = MAX(0.7, gKbF * 0.97); gKbSentT = 0; }   // لم تكمل بعده: الإرسال كان صحيحاً → أسرع قليلاً
        });
        if (gKbHaptic) { UIImpactFeedbackGenerator *g = [[UIImpactFeedbackGenerator alloc] initWithStyle:UIImpactFeedbackStyleMedium]; [g impactOccurred]; }
        DSKbSendNow(f);
    });
}

// ---- إرسال تلقائي عند اكتمال عدد من الأرقام (يحل محل «الاوجود»): كل ما تكتبه بحقل دردشة اللعبة أرقام فقط وعددها = N يُرسل تلقائياً
static BOOL DSDigitSendIsOn(void) { return [NSUserDefaults.standardUserDefaults boolForKey:@"DSDigitSendOn"]; }
static NSInteger DSDigitSendN(void) {
    id v = [NSUserDefaults.standardUserDefaults objectForKey:@"DSDigitSendN"];
    NSInteger n = v ? [v integerValue] : 12;
    return MAX(1, MIN(40, n));
}
static void DSDigitSendSetN(NSInteger n) { [NSUserDefaults.standardUserDefaults setInteger:MAX(1, MIN(40, n)) forKey:@"DSDigitSendN"]; }
static NSString *DSDigitSendTitle(void) {
    return DSDigitSendIsOn() ? [NSString stringWithFormat:@"إرسال عند اكتمال %ld رقم: ON", (long)DSDigitSendN()] : @"إرسال عند اكتمال الأرقام: OFF";
}
static void DSDigitSendToggle(void) { [NSUserDefaults.standardUserDefaults setBool:!DSDigitSendIsOn() forKey:@"DSDigitSendOn"]; }
// النص كله أرقام (مع مسافات/نقاط من أوضاع الأرقام) وعدد الأرقام = N بالضبط؟
static BOOL DSDigitComplete(NSString *t) {
    if (!t.length) return NO;
    NSInteger digits = 0;
    for (NSUInteger i = 0; i < t.length; i++) {
        unichar c = [t characterAtIndex:i];
        if (DSKbIsDigit(c)) digits++;
        else if (c != ' ' && c != '.') return NO;
    }
    return digits == DSDigitSendN();
}
static void DSDigitSendCheck(id t, NSString *text) {
    if (!DSDigitSendIsOn() || gKbBusy || !text.length || ![NSThread isMainThread] || !DSKbSenseFieldOK(t)) return;
    NSString *cur = [t isKindOfClass:UITextField.class] ? ((UITextField *)t).text : ((UITextView *)t).text;
    if (!DSDigitComplete(cur)) return;
    __weak id wt = t;
    dispatch_async(dispatch_get_main_queue(), ^{   // بعد ما تكمل اللعبة معالجة الإدخال
        id st = wt;
        if (!st || !DSDigitComplete([st isKindOfClass:UITextField.class] ? ((UITextField *)st).text : ((UITextView *)st).text)) return;
        gKbSenseGen++;   // يلغي مؤقّت الإرسال التلقائي القديم حتى ما يرسل مرتين
        DSKbSendNow(st);
    });
}

// بعد كل إدخال: سجّل نبض الكتابة وأعد ضبط العدّ
static void DSKbAfterInsert(id t, NSString *text) {
    DSDigitSendCheck(t, text);   // إرسال عند اكتمال الأرقام (مستقل عن حساسية الإرسال التلقائي)
    if (!gKbSense || gKbBusy || !text.length || ![NSThread isMainThread] || !DSKbSenseFieldOK(t)) return;
    if ([text isEqualToString:@"\n"]) { gKbSenseGen++; gKbDirty = NO; return; }   // أرسلتَ بنفسك
    double now = DSNow();
    int idx = DSKbAllDigits(text) ? 0 : 1; gKbLastIdx = idx;
    if (gKbLastKeyT > 0 && now - gKbLastKeyT < 1.5) {
        double g = now - gKbLastKeyT;
        gKbAvgGap = gKbAvgGap > 0 ? gKbAvgGap * 0.5 + g * 0.5 : g;
        double m = gKbMean[idx];
        gKbMean[idx] = m > 0 ? m * 0.6 + g * 0.4 : g;
        double dv = g - gKbMean[idx];
        gKbVar[idx] = gKbVar[idx] * 0.6 + dv * dv * 0.4;
    }
    // إرسال مبكر؟ كتبت بعد الإرسال مباشرة والحقل ما زال فيه نص قديم → ابطئ قليلاً
    if (gKbSentT > 0) {
        NSString *cur = [t isKindOfClass:UITextField.class] ? ((UITextField *)t).text : ((UITextView *)t).text;
        if (now - gKbSentT < 0.8 && cur.length > text.length) gKbF = MIN(3.0, gKbF * 1.25);
        gKbSentT = 0;
    }
    gKbLastKeyT = now; gKbField = t; gKbDirty = YES;
    DSKbSenseArmN(0);
}

static void DSKbAfterDelete(id t) {
    if (!gKbSense || gKbBusy || ![NSThread isMainThread] || !DSKbSenseFieldOK(t)) return;
    gKbLastKeyT = DSNow(); gKbField = t;
    if (gKbDirty) DSKbSenseArmN(0);
}

static void DSKbCancel(void) { if (!gKbBusy && gKbSense) gKbSenseGen++; }

// تتبّع اللمس فوق منطقة الكيبورد (للكيبورد الذي يمر لمسه عبر نافذة التطبيق)
static void DSKbTrackTouches(UIEvent *e) {
    if (!gKbSense || e.type != UIEventTypeTouches || CGRectIsEmpty(gKbFrame)) return;
    BOOL any = NO;
    for (UITouch *t in e.allTouches) {
        if (t.phase == UITouchPhaseEnded || t.phase == UITouchPhaseCancelled) continue;
        UIWindow *w = t.window; if (!w) continue;
        CGPoint sp = [UIScreen.mainScreen.coordinateSpace convertPoint:[t locationInView:w] fromCoordinateSpace:w];
        if (CGRectContainsPoint(gKbFrame, sp)) { any = YES; break; }
    }
    if (any) { gKbTouching = YES; gKbSenseGen++; }            // ما دام اصبعك على الكيبورد: لا إرسال
    else if (gKbTouching) {                                    // رفعت يدك
        gKbTouching = NO;
        if (gKbDirty) DSKbSenseArmN(0);
    }
}

static void DSKbInstallFrameObservers(void) {
    NSNotificationCenter *nc = NSNotificationCenter.defaultCenter;
    [nc addObserverForName:UIKeyboardWillChangeFrameNotification object:nil queue:NSOperationQueue.mainQueue usingBlock:^(NSNotification *n) {
        NSValue *v = n.userInfo[UIKeyboardFrameEndUserInfoKey];
        if (v) gKbFrame = v.CGRectValue;
    }];
    [nc addObserverForName:UIKeyboardWillHideNotification object:nil queue:NSOperationQueue.mainQueue usingBlock:^(NSNotification *n) {
        gKbFrame = CGRectZero; gKbTouching = NO; gKbSenseGen++;
    }];
}

%group DSKeyboardHooks

%hook UITextField
- (void)insertText:(NSString *)text {
    NSUInteger del = 0; NSString *rep = nil;
    if (DSKbPlanInsert(self, text, &del, &rep)) {
        gKbBusy = YES;
        for (NSUInteger i = 0; i < del; i++) [self deleteBackward];
        gKbBusy = NO;
        %orig(rep);
    } else {
        %orig;
    }
    DSKbAfterInsert(self, text);
}
- (void)deleteBackward {
    DSKbCancel();
    NSUInteger del = 0; NSString *rep = nil;
    if (DSKbPlanDelete(self, &del, &rep)) {
        gKbBusy = YES;
        for (NSUInteger i = 0; i < del; i++) %orig;
        if (rep.length) [self insertText:rep];
        gKbBusy = NO;
    } else {
        %orig;
    }
    DSKbAfterDelete(self);
}
%end

%hook UITextView
- (void)insertText:(NSString *)text {
    NSUInteger del = 0; NSString *rep = nil;
    if (DSKbPlanInsert(self, text, &del, &rep)) {
        gKbBusy = YES;
        for (NSUInteger i = 0; i < del; i++) [self deleteBackward];
        gKbBusy = NO;
        %orig(rep);
    } else {
        %orig;
    }
    DSKbAfterInsert(self, text);
}
- (void)deleteBackward {
    DSKbCancel();
    NSUInteger del = 0; NSString *rep = nil;
    if (DSKbPlanDelete(self, &del, &rep)) {
        gKbBusy = YES;
        for (NSUInteger i = 0; i < del; i++) %orig;
        if (rep.length) [self insertText:rep];
        gKbBusy = NO;
    } else {
        %orig;
    }
    DSKbAfterDelete(self);
}
%end

%hook UIApplication
- (void)sendEvent:(UIEvent *)event {
    %orig;
    DSKbTrackTouches(event);
}
%end

%end


#pragma mark - أداة متصفح: Number Sender (HTML/JS كما سُلّم تماماً، بدون أي تعديل — base64 لتفادي أي التباس في الرموز)

static NSString *DSNumberSenderHTML(void) {
    NSString *b64 =
    @"DQo8IURPQ1RZUEUgaHRtbD4NCjxodG1sIGxhbmc9ImFyIiBkaXI9InJ0bCI+DQo8aGVhZD4NCjxtZXRhIGNoYXJzZXQ9IlVURi04Ij4NCjxtZXRhIG5hbWU9InZpZXdwb3J0IiBjb250ZW50PSJ3aWR0aD1kZXZpY2Utd2lkdGgsIGluaXRpYWwtc2NhbGU9MSI+DQo8bWV0YSBuYW1lPSJ0aGVtZS1jb2xvciIgY29udGVudD0iIzFlMjkzYiI+DQo8dGl0bGU+TnVtYmVyIFNlbmRlcjwvdGl0bGU+DQo8c3R5bGU+DQo6cm9vdHstLWJnOiNmMWY0Zjk7LS1kYXJrOiMxZTI5M2I7LS1ibHVlOiMzYjgyZjY7LS1ncmVlbjojMjJjNTVlOy0t"
    @"Z3JheTojOTRhM2I4Oy0tcmVkOiNlZjQ0NDQ7LS10ZXh0OiMxZTI5M2I7LS1tdXRlZDojNjQ3NDhifQ0KKntib3gtc2l6aW5nOmJvcmRlci1ib3h9DQpib2R5e21hcmdpbjowO2JhY2tncm91bmQ6dmFyKC0tYmcpO2ZvbnQtZmFtaWx5OkFyaWFsLCJTZWdvZSBVSSIsc2Fucy1zZXJpZjtjb2xvcjp2YXIoLS10ZXh0KTttaW4taGVpZ2h0OjEwMHZoO2Rpc3BsYXk6Z3JpZDtwbGFjZS1pdGVtczpjZW50ZXI7cGFkZGluZzoyMHB4fQ0KLmFwcHt3aWR0aDptaW4oNDAwcHgsMTAwJSk7YmFja2dyb3VuZDp2YXIoLS1iZyk7b3ZlcmZsb3c6"
    @"aGlkZGVufQ0KaGVhZGVye2hlaWdodDo3OXB4O2JhY2tncm91bmQ6dmFyKC0tZGFyayk7Ym9yZGVyLWJvdHRvbTozcHggc29saWQgdmFyKC0tYmx1ZSk7Y29sb3I6d2hpdGU7dGV4dC1hbGlnbjpjZW50ZXI7cGFkZGluZzoxMHB4fQ0KaGVhZGVyIGgxe2ZvbnQtc2l6ZToyNXB4O21hcmdpbjowIDAgNXB4fQ0KaGVhZGVyIHB7Zm9udC1zaXplOjEzcHg7Y29sb3I6I2E1YjRjODttYXJnaW46MH0NCm1haW57cGFkZGluZzoxM3B4IDIwcHggMH0NCi5zdGF0dXN7aGVpZ2h0OjY2cHg7YmFja2dyb3VuZDp3aGl0ZTtib3JkZXItcmFkaXVz"
    @"OjhweDtkaXNwbGF5OmdyaWQ7Z3JpZC10ZW1wbGF0ZS1jb2x1bW5zOjFmciAxZnI7YWxpZ24taXRlbXM6Y2VudGVyO21hcmdpbi1ib3R0b206MTJweH0NCi5zdGF0e3RleHQtYWxpZ246Y2VudGVyfQ0KLnN0YXQ6Zmlyc3QtY2hpbGR7Ym9yZGVyLWxlZnQ6MXB4IHNvbGlkICNlMmU4ZjB9DQouYmlne2ZvbnQtc2l6ZToyOHB4O2ZvbnQtd2VpZ2h0OmJvbGQ7Y29sb3I6dmFyKC0tYmx1ZSl9DQouc21hbGx7Zm9udC1zaXplOjEycHg7Y29sb3I6dmFyKC0tbXV0ZWQpO21hcmdpbi10b3A6M3B4fQ0KLnBpbGx7ZGlzcGxheTppbmxpbmUt"
    @"YmxvY2s7YmFja2dyb3VuZDp2YXIoLS1ncmF5KTtjb2xvcjp3aGl0ZTtib3JkZXItcmFkaXVzOjVweDtwYWRkaW5nOjdweCAxOHB4O2ZvbnQtd2VpZ2h0OmJvbGQ7Zm9udC1zaXplOjEzcHh9DQouc2VjdGlvbi10aXRsZXtmb250LXNpemU6MTRweDtmb250LXdlaWdodDpib2xkO21hcmdpbjoxM3B4IDAgOHB4fQ0KLnByZXNldC1saXN0e2hlaWdodDoxNTBweDtvdmVyZmxvdzphdXRvO2JhY2tncm91bmQ6d2hpdGU7Ym9yZGVyOjFweCBzb2xpZCAjZGJlMmVhO2JvcmRlci1yYWRpdXM6N3B4fQ0KLnByZXNldHtkaXNwbGF5OmdyaWQ7"
    @"Z3JpZC10ZW1wbGF0ZS1jb2x1bW5zOjFmciAxMDBweDtwYWRkaW5nOjhweCAxMXB4O2JvcmRlci1ib3R0b206MXB4IHNvbGlkICNlZGYwZjQ7Y3Vyc29yOnBvaW50ZXI7Zm9udC1zaXplOjEzcHh9DQoucHJlc2V0Omxhc3QtY2hpbGR7Ym9yZGVyOjB9DQoucHJlc2V0OmhvdmVye2JhY2tncm91bmQ6I2VmZjZmZn0NCi5wcmVzZXQuYWN0aXZle2JhY2tncm91bmQ6I2RiZWFmZTtjb2xvcjojMWQ0ZWQ4O2ZvbnQtd2VpZ2h0OmJvbGR9DQoucHJlc2V0IHNwYW46bGFzdC1jaGlsZHt0ZXh0LWFsaWduOmNlbnRlcn0NCi5jdXN0b217ZGlz"
    @"cGxheTpmbGV4O2dhcDoxMHB4O21hcmdpbi10b3A6OHB4fQ0KaW5wdXRbdHlwZT1udW1iZXJde3dpZHRoOjEyMHB4O2hlaWdodDozNnB4O2JvcmRlcjoxcHggc29saWQgI2NiZDVlMTtib3JkZXItcmFkaXVzOjZweDt0ZXh0LWFsaWduOmNlbnRlcjtmb250LXNpemU6MTVweDtiYWNrZ3JvdW5kOndoaXRlfQ0KYnV0dG9ue2JvcmRlcjowO2JvcmRlci1yYWRpdXM6NnB4O2N1cnNvcjpwb2ludGVyO2ZvbnQ6aW5oZXJpdH0NCi5hcHBseXtmbGV4OjE7YmFja2dyb3VuZDp2YXIoLS1ibHVlKTtjb2xvcjp3aGl0ZTtmb250LXdlaWdodDpi"
    @"b2xkfQ0KLmFwcGx5OmhvdmVye2JhY2tncm91bmQ6IzI1NjNlYn0NCi50b2dnbGUtcm93e2hlaWdodDo0OHB4O2JhY2tncm91bmQ6d2hpdGU7Ym9yZGVyLXJhZGl1czo4cHg7bWFyZ2luLXRvcDoxMHB4O3BhZGRpbmc6NnB4IDEycHg7ZGlzcGxheTpmbGV4O2FsaWduLWl0ZW1zOmNlbnRlcjtqdXN0aWZ5LWNvbnRlbnQ6c3BhY2UtYmV0d2VlbjtjdXJzb3I6cG9pbnRlcn0NCi50b2dnbGUtY29weXt0ZXh0LWFsaWduOnJpZ2h0fQ0KLnRvZ2dsZS1jb3B5IHN0cm9uZ3tkaXNwbGF5OmJsb2NrO2ZvbnQtc2l6ZToxM3B4fQ0KLnRvZ2ds"
    @"ZS1jb3B5IHNtYWxse2ZvbnQtc2l6ZToxMXB4O2NvbG9yOnZhcigtLW11dGVkKX0NCi5zd2l0Y2h7d2lkdGg6NDhweDtoZWlnaHQ6MjVweDtiYWNrZ3JvdW5kOnZhcigtLWdyYXkpO2JvcmRlci1yYWRpdXM6MjBweDtwb3NpdGlvbjpyZWxhdGl2ZTtmbGV4Om5vbmV9DQouc3dpdGNoOmFmdGVye2NvbnRlbnQ6IiI7cG9zaXRpb246YWJzb2x1dGU7d2lkdGg6MTlweDtoZWlnaHQ6MTlweDt0b3A6M3B4O3JpZ2h0OjNweDtiYWNrZ3JvdW5kOndoaXRlO2JvcmRlci1yYWRpdXM6NTAlO3RyYW5zaXRpb246LjE1c30NCi5zd2l0Y2gub257"
    @"YmFja2dyb3VuZDp2YXIoLS1ncmVlbil9DQouc3dpdGNoLm9uOmFmdGVye3JpZ2h0OjI2cHh9DQpmb290ZXJ7dGV4dC1hbGlnbjpjZW50ZXI7Y29sb3I6dmFyKC0tbXV0ZWQpO2ZvbnQtc2l6ZToxMXB4O3BhZGRpbmc6MTVweCAwIDEwcHh9DQpmb290ZXIgLmhpbnR7Zm9udC1zaXplOjEwcHg7Y29sb3I6Izk0YTNiODttYXJnaW4tdG9wOjRweH0NCi5wcmV2aWV3e21hcmdpbi10b3A6MTJweDtiYWNrZ3JvdW5kOndoaXRlO2JvcmRlci1yYWRpdXM6OHB4O3BhZGRpbmc6MTBweH0NCi5wcmV2aWV3IGxhYmVse2ZvbnQtc2l6ZToxMnB4"
    @"O2NvbG9yOnZhcigtLW11dGVkKX0NCi5wcmV2aWV3LXZhbHVle2ZvbnQtc2l6ZToxOXB4O2xldHRlci1zcGFjaW5nOjJweDtkaXJlY3Rpb246bHRyO3RleHQtYWxpZ246Y2VudGVyO21pbi1oZWlnaHQ6MjVweDttYXJnaW46NnB4IDA7d29yZC1icmVhazpicmVhay1hbGx9DQouYWN0aW9uc3tkaXNwbGF5OmZsZXg7Z2FwOjhweH0NCi5hY3Rpb25zIGJ1dHRvbntoZWlnaHQ6MzZweDtmbGV4OjE7Zm9udC13ZWlnaHQ6Ym9sZH0NCi5zZW5ke2JhY2tncm91bmQ6dmFyKC0tZ3JlZW4pO2NvbG9yOndoaXRlfQ0KLmNsZWFye2JhY2tncm91"
    @"bmQ6I2UyZThmMDtjb2xvcjp2YXIoLS1kYXJrKX0NCi5ub3Rle2ZvbnQtc2l6ZToxMXB4O2NvbG9yOnZhcigtLW11dGVkKTtsaW5lLWhlaWdodDoxLjY7bWFyZ2luOjEwcHggMCAwfQ0KI3RvYXN0e3Bvc2l0aW9uOmZpeGVkO2JvdHRvbToxOHB4O2xlZnQ6NTAlO3RyYW5zZm9ybTp0cmFuc2xhdGVYKC01MCUpO2JhY2tncm91bmQ6dmFyKC0tZGFyayk7Y29sb3I6d2hpdGU7cGFkZGluZzo5cHggMTVweDtib3JkZXItcmFkaXVzOjdweDtmb250LXNpemU6MTJweDtvcGFjaXR5OjA7cG9pbnRlci1ldmVudHM6bm9uZTt0cmFuc2l0aW9u"
    @"Om9wYWNpdHkgLjJzfQ0KI3RvYXN0LnNob3d7b3BhY2l0eToxfQ0KPC9zdHlsZT4NCjwvaGVhZD4NCjxib2R5Pg0KPGRpdiBjbGFzcz0iYXBwIj4NCjxoZWFkZXI+PGgxPk51bWJlciBTZW5kZXI8L2gxPjxwPtmF2LHYs9mEINin2YTYo9ix2YLYp9mFINin2YTYqtmE2YLYp9im2Yo8L3A+PC9oZWFkZXI+DQo8bWFpbj4NCjxzZWN0aW9uIGNsYXNzPSJzdGF0dXMiPg0KPGRpdiBjbGFzcz0ic3RhdCI+PGRpdiBjbGFzcz0iYmlnIiBpZD0ibGVuZ3RoVmlldyI+MTI8L2Rpdj48ZGl2IGNsYXNzPSJzbWFsbCI+2LnYr9ivINin2YTYrtin"
    @"2YbYp9iqPC9kaXY+PC9kaXY+DQo8ZGl2IGNsYXNzPSJzdGF0Ij48ZGl2IGNsYXNzPSJwaWxsIiBpZD0ic3RhdGVQaWxsIj7Zhdiq2YjZgtmBPC9kaXY+PGRpdiBjbGFzcz0ic21hbGwiPtin2YTYrdin2YTYqTwvZGl2PjwvZGl2Pg0KPC9zZWN0aW9uPg0KDQo8ZGl2IGNsYXNzPSJzZWN0aW9uLXRpdGxlIj7Yp9mE2K7Zitin2LHYp9iqINin2YTYrNin2YfYstipPC9kaXY+DQo8ZGl2IGNsYXNzPSJwcmVzZXQtbGlzdCIgaWQ9InByZXNldExpc3QiPjwvZGl2Pg0KDQo8ZGl2IGNsYXNzPSJzZWN0aW9uLXRpdGxlIj7Yudiv2K8g2YXY"
    @"rti12LU8L2Rpdj4NCjxkaXYgY2xhc3M9ImN1c3RvbSI+DQo8aW5wdXQgaWQ9Imxlbmd0aElucHV0IiB0eXBlPSJudW1iZXIiIG1pbj0iMSIgbWF4PSIxMDAiIHZhbHVlPSIxMiI+DQo8YnV0dG9uIGNsYXNzPSJhcHBseSIgaWQ9ImFwcGx5QnRuIj7Yqti32KjZitmCPC9idXR0b24+DQo8L2Rpdj4NCg0KPGRpdiBjbGFzcz0idG9nZ2xlLXJvdyIgaWQ9ImVuYWJsZVJvdyIgcm9sZT0iYnV0dG9uIiB0YWJpbmRleD0iMCI+DQo8ZGl2IGNsYXNzPSJ0b2dnbGUtY29weSI+PHN0cm9uZz7YqtmB2LnZitmEINin2YTYpdix2LPYp9mEINin"
    @"2YTYqtmE2YLYp9im2Yo8L3N0cm9uZz48c21hbGw+2KXYr9iu2KfZhCDYqtmE2YLYp9im2Yog2LnZhtivINin2YPYqtmF2KfZhCDYp9mE2KPYsdmC2KfZhTwvc21hbGw+PC9kaXY+DQo8ZGl2IGNsYXNzPSJzd2l0Y2giIGlkPSJlbmFibGVTd2l0Y2giPjwvZGl2Pg0KPC9kaXY+DQoNCjxkaXYgY2xhc3M9InRvZ2dsZS1yb3ciIGlkPSJtb3VzZVJvdyIgcm9sZT0iYnV0dG9uIiB0YWJpbmRleD0iMCI+DQo8ZGl2IGNsYXNzPSJ0b2dnbGUtY29weSI+PHN0cm9uZz7Ytti62Lcg2KfZhNmF2KfZiNizINi52YbYryDYp9mE2KfZg9iq2YXY"
    @"p9mEPC9zdHJvbmc+PHNtYWxsPtil2LHYs9in2YQg2KfZhNix2YLZhSDYq9mFINiq2YbZgdmK2LAg2YbZgtix2Kkg2K/Yp9iu2YQg2KfZhNi12YHYrdipPC9zbWFsbD48L2Rpdj4NCjxkaXYgY2xhc3M9InN3aXRjaCIgaWQ9Im1vdXNlU3dpdGNoIj48L2Rpdj4NCjwvZGl2Pg0KDQo8c2VjdGlvbiBjbGFzcz0icHJldmlldyI+DQo8bGFiZWwgZm9yPSJudW1iZXJJbnB1dCI+2KzYsdmR2Kgg2KXYr9iu2KfZhCDYp9mE2KPYsdmC2KfZhSDZh9mG2Kc8L2xhYmVsPg0KPGlucHV0IGlkPSJudW1iZXJJbnB1dCIgdHlwZT0idGV4dCIgaW5w"
    @"dXRtb2RlPSJudW1lcmljIiBhdXRvY29tcGxldGU9Im9mZiIgcGxhY2Vob2xkZXI9Itin2YPYqtioINin2YTYo9ix2YLYp9mFLi4uIiBzdHlsZT0id2lkdGg6MTAwJTtoZWlnaHQ6MzhweDttYXJnaW4tdG9wOjdweDt0ZXh0LWFsaWduOmxlZnQ7ZGlyZWN0aW9uOmx0cjtwYWRkaW5nOjAgMTBweCI+DQo8ZGl2IGNsYXNzPSJzbWFsbCIgc3R5bGU9InRleHQtYWxpZ246Y2VudGVyO21hcmdpbi10b3A6N3B4Ij7Yp9mE2LnYr9ivINin2YTYrdin2YTZijogPGIgaWQ9ImNvdW50VmlldyI+MDwvYj48L2Rpdj4NCjxkaXYgY2xhc3M9ImFj"
    @"dGlvbnMiIHN0eWxlPSJtYXJnaW4tdG9wOjlweCI+DQo8YnV0dG9uIGNsYXNzPSJzZW5kIiBpZD0ic2VuZEJ0biI+2KXYsdiz2KfZhCDYp9mE2KLZhjwvYnV0dG9uPg0KPGJ1dHRvbiBjbGFzcz0iY2xlYXIiIGlkPSJjbGVhckJ0biI+2YXYs9itPC9idXR0b24+DQo8L2Rpdj4NCjxwIGNsYXNzPSJub3RlIj7Yqti52YXZhCDZh9iw2Ycg2KfZhNmG2LPYrtipINiv2KfYrtmEINi12YHYrdipINin2YTZhdiq2LXZgditINmB2YLYty4g2YTYpyDZitmF2YPZhiDZhNi12YHYrdipIEphdmFTY3JpcHQg2LnYp9iv2YrYqSDYp9mE2KrYrdmD"
    @"2YUg2KjZhNmI2K3YqSDYp9mE2YXZgdin2KrZititINij2Ygg2KfZhNmG2YLYsSDZgdmKINin2YTYqti32KjZitmC2KfYqiDYp9mE2KPYrtix2YkuPC9wPg0KPC9zZWN0aW9uPg0KPC9tYWluPg0KPGZvb3Rlcj5OdW1iZXIgU2VuZGVyPGRpdiBjbGFzcz0iaGludCI+SmF2YVNjcmlwdDwvZGl2PjwvZm9vdGVyPg0KPC9kaXY+DQoNCjxkaXYgaWQ9InRvYXN0Ij48L2Rpdj4NCg0KPHNjcmlwdD4NCiJ1c2Ugc3RyaWN0IjsNCg0KY29uc3QgJCA9IGlkID0+IGRvY3VtZW50LmdldEVsZW1lbnRCeUlkKGlkKTsNCg0KbGV0IHRhcmdldExl"
    @"bmd0aCA9IDEyOw0KbGV0IGVuYWJsZWQgPSBmYWxzZTsNCmxldCBtb3VzZUVuYWJsZWQgPSBmYWxzZTsNCmxldCBkaWdpdHMgPSAiIjsNCg0KY29uc3QgcHJlc2V0cyA9IFsNClsi2LnYtNix2KfYqiIsMl0sWyLZhdim2KfYqiIsM10sWyLYotmE2KfZgSIsNF0sDQpbIti52LTYsdin2Kog2KfZhNii2YTYp9mBIiw1XSxbItmF2KbYp9iqINin2YTYotmE2KfZgSIsNl0sDQpbItmF2YTZitmI2YYiLDddLFsi2LnYtNix2Kkg2YXZhNin2YrZitmGIiw4XSxbItmF2KbYqSDZhdmE2YrZiNmGIiw5XSwNClsi2YXZhNmK2KfYsSIsMTBdLFsi"
    @"2LnYtNix2Kkg2YXZhNmK2KfYsdin2KoiLDExXSxbItmF2KbYqSDZhdmE2YrYp9ixIiwxMl0sDQpbItiq2LHZitmE2YrZiNmGIiwxM10sWyLYudi02LHYqSDYqtix2YrZhNmK2YjZhtin2KoiLDE0XSwNClsi2YXYptipINiq2LHZitmE2YrZiNmGIiwxNV0sWyLZg9mI2KfYr9ix2YrZhNmK2YjZhiIsMTZdLA0KWyLZg9mI2YrZhtiq2YTZitmI2YYiLDE5XSxbItiz2YPYs9iq2YTZitmI2YYiLDIyXQ0KXTsNCg0KZnVuY3Rpb24gc2hvd1RvYXN0KG1lc3NhZ2Upew0KY29uc3QgdG9hc3Q9JCgidG9hc3QiKTsNCnRvYXN0LnRleHRDb250"
    @"ZW50PW1lc3NhZ2U7DQp0b2FzdC5jbGFzc0xpc3QuYWRkKCJzaG93Iik7DQpjbGVhclRpbWVvdXQoc2hvd1RvYXN0LnRpbWVyKTsNCnNob3dUb2FzdC50aW1lcj1zZXRUaW1lb3V0KCgpPT50b2FzdC5jbGFzc0xpc3QucmVtb3ZlKCJzaG93IiksMTcwMCk7DQp9DQoNCmZ1bmN0aW9uIHJlbmRlclByZXNldHMoKXsNCiQoInByZXNldExpc3QiKS5pbm5lckhUTUw9IiI7DQpwcmVzZXRzLmZvckVhY2goKFtuYW1lLGNvdW50XSk9PnsNCmNvbnN0IHJvdz1kb2N1bWVudC5jcmVhdGVFbGVtZW50KCJkaXYiKTsNCnJvdy5jbGFzc05hbWU9"
    @"InByZXNldCIrKGNvdW50PT09dGFyZ2V0TGVuZ3RoPyIgYWN0aXZlIjoiIik7DQpjb25zdCB0aXRsZT1kb2N1bWVudC5jcmVhdGVFbGVtZW50KCJzcGFuIik7DQpjb25zdCBudW1iZXI9ZG9jdW1lbnQuY3JlYXRlRWxlbWVudCgic3BhbiIpOw0KdGl0bGUudGV4dENvbnRlbnQ9bmFtZTsNCm51bWJlci50ZXh0Q29udGVudD1jb3VudCsiINiu2KfZhtipIjsNCnJvdy5hcHBlbmQodGl0bGUsbnVtYmVyKTsNCnJvdy5hZGRFdmVudExpc3RlbmVyKCJjbGljayIsKCk9PnNldExlbmd0aChjb3VudCkpOw0KJCgicHJlc2V0TGlzdCIpLmFw"
    @"cGVuZENoaWxkKHJvdyk7DQp9KTsNCn0NCg0KZnVuY3Rpb24gc2V0TGVuZ3RoKHZhbHVlKXsNCmNvbnN0IG49TnVtYmVyKHZhbHVlKTsNCmlmKCFOdW1iZXIuaXNJbnRlZ2VyKG4pfHxuPDF8fG4+MTAwKXsNCnNob3dUb2FzdCgi2KPYr9iu2YQg2LnYr9iv2YvYpyDZhdmGIDEg2KXZhNmJIDEwMCIpOw0KcmV0dXJuOw0KfQ0KdGFyZ2V0TGVuZ3RoPW47DQpkaWdpdHM9IiI7DQokKCJsZW5ndGhJbnB1dCIpLnZhbHVlPW47DQokKCJsZW5ndGhWaWV3IikudGV4dENvbnRlbnQ9bjsNCiQoIm51bWJlcklucHV0IikudmFsdWU9IiI7DQp1"
    @"cGRhdGVDb3VudCgpOw0KcmVuZGVyUHJlc2V0cygpOw0KfQ0KDQpmdW5jdGlvbiB1cGRhdGVDb3VudCgpew0KJCgiY291bnRWaWV3IikudGV4dENvbnRlbnQ9ZGlnaXRzLmxlbmd0aDsNCn0NCg0KZnVuY3Rpb24gdXBkYXRlU3RhdHVzKCl7DQokKCJlbmFibGVTd2l0Y2giKS5jbGFzc0xpc3QudG9nZ2xlKCJvbiIsZW5hYmxlZCk7DQokKCJtb3VzZVN3aXRjaCIpLmNsYXNzTGlzdC50b2dnbGUoIm9uIixtb3VzZUVuYWJsZWQpOw0KJCgic3RhdGVQaWxsIikudGV4dENvbnRlbnQ9ZW5hYmxlZD8obW91c2VFbmFibGVkPyLZiti52YXZ"
    @"hCDZhdi5INin2YTZhtmC2LEiOiLZiti52YXZhCIpOiLZhdiq2YjZgtmBIjsNCiQoInN0YXRlUGlsbCIpLnN0eWxlLmJhY2tncm91bmQ9ZW5hYmxlZD8idmFyKC0tZ3JlZW4pIjoidmFyKC0tZ3JheSkiOw0KfQ0KDQpmdW5jdGlvbiB0b2dnbGVFbmFibGVkKCl7DQplbmFibGVkPSFlbmFibGVkOw0KZGlnaXRzPSIiOw0KdXBkYXRlQ291bnQoKTsNCnVwZGF0ZVN0YXR1cygpOw0KfQ0KDQpmdW5jdGlvbiB0b2dnbGVNb3VzZSgpew0KbW91c2VFbmFibGVkPSFtb3VzZUVuYWJsZWQ7DQp1cGRhdGVTdGF0dXMoKTsNCn0NCg0KZnVuY3Rp"
    @"b24gZGVsaXZlcih2YWx1ZSl7DQpjb25zdCBmaWVsZD0kKCJudW1iZXJJbnB1dCIpOw0KZmllbGQudmFsdWU9dmFsdWU7DQoNCmZpZWxkLmRpc3BhdGNoRXZlbnQobmV3IEN1c3RvbUV2ZW50KCJudW1iZXItc2VudCIsew0KYnViYmxlczp0cnVlLA0KZGV0YWlsOnsNCnZhbHVlLA0KYWN0aW9uOm1vdXNlRW5hYmxlZD8iY2xpY2siOiJlbnRlciINCn0NCn0pKTsNCg0KaWYobW91c2VFbmFibGVkKXsNCmZpZWxkLmRpc3BhdGNoRXZlbnQobmV3IE1vdXNlRXZlbnQoImNsaWNrIix7YnViYmxlczp0cnVlfSkpOw0KfWVsc2V7DQpmaWVs"
    @"ZC5kaXNwYXRjaEV2ZW50KG5ldyBLZXlib2FyZEV2ZW50KCJrZXlkb3duIix7DQprZXk6IkVudGVyIixjb2RlOiJFbnRlciIsYnViYmxlczp0cnVlDQp9KSk7DQpmaWVsZC5kaXNwYXRjaEV2ZW50KG5ldyBLZXlib2FyZEV2ZW50KCJrZXl1cCIsew0Ka2V5OiJFbnRlciIsY29kZToiRW50ZXIiLGJ1YmJsZXM6dHJ1ZQ0KfSkpOw0KfQ0KDQpzaG93VG9hc3QobW91c2VFbmFibGVkPw0KItiq2YUg2KfZhNil2LHYs9in2YQg2YjYqtmG2YHZitiwINmG2YLYsdipINiv2KfYrtmEINin2YTYtdmB2K3YqSI6DQoi2KrZhSDYp9mE2KXYsdiz"
    @"2KfZhCDYr9in2K7ZhCDYp9mE2LXZgdit2KkiKTsNCn0NCg0KZnVuY3Rpb24gcHJvY2Vzc0lucHV0KHJhdyl7DQpjb25zdCBvbmx5RGlnaXRzPXJhdy5yZXBsYWNlKC9bXjAtOV0vZywiIik7DQoNCmlmKCFlbmFibGVkKXsNCmRpZ2l0cz1vbmx5RGlnaXRzLnNsaWNlKC10YXJnZXRMZW5ndGgpOw0KdXBkYXRlQ291bnQoKTsNCnJldHVybjsNCn0NCg0KZGlnaXRzPW9ubHlEaWdpdHMuc2xpY2UoLXRhcmdldExlbmd0aCk7DQp1cGRhdGVDb3VudCgpOw0KDQppZihkaWdpdHMubGVuZ3RoPj10YXJnZXRMZW5ndGgpew0KY29uc3QgY29t"
    @"cGxldGVkPWRpZ2l0czsNCmRpZ2l0cz0iIjsNCnVwZGF0ZUNvdW50KCk7DQpkZWxpdmVyKGNvbXBsZXRlZCk7DQp9DQp9DQoNCiQoImFwcGx5QnRuIikuYWRkRXZlbnRMaXN0ZW5lcigiY2xpY2siLCgpPT57DQpzZXRMZW5ndGgoJCgibGVuZ3RoSW5wdXQiKS52YWx1ZSk7DQp9KTsNCg0KJCgibGVuZ3RoSW5wdXQiKS5hZGRFdmVudExpc3RlbmVyKCJrZXlkb3duIixlPT57DQppZihlLmtleT09PSJFbnRlciIpc2V0TGVuZ3RoKCQoImxlbmd0aElucHV0IikudmFsdWUpOw0KfSk7DQoNCiQoImVuYWJsZVJvdyIpLmFkZEV2ZW50TGlz"
    @"dGVuZXIoImNsaWNrIix0b2dnbGVFbmFibGVkKTsNCiQoImVuYWJsZVJvdyIpLmFkZEV2ZW50TGlzdGVuZXIoImtleWRvd24iLGU9PnsNCmlmKGUua2V5PT09IkVudGVyInx8ZS5rZXk9PT0iICIpdG9nZ2xlRW5hYmxlZCgpOw0KfSk7DQoNCiQoIm1vdXNlUm93IikuYWRkRXZlbnRMaXN0ZW5lcigiY2xpY2siLHRvZ2dsZU1vdXNlKTsNCiQoIm1vdXNlUm93IikuYWRkRXZlbnRMaXN0ZW5lcigia2V5ZG93biIsZT0+ew0KaWYoZS5rZXk9PT0iRW50ZXIifHxlLmtleT09PSIgIil0b2dnbGVNb3VzZSgpOw0KfSk7DQoNCiQoIm51bWJl"
    @"cklucHV0IikuYWRkRXZlbnRMaXN0ZW5lcigiaW5wdXQiLGU9PnsNCnByb2Nlc3NJbnB1dChlLnRhcmdldC52YWx1ZSk7DQp9KTsNCg0KJCgibnVtYmVySW5wdXQiKS5hZGRFdmVudExpc3RlbmVyKCJrZXlkb3duIixlPT57DQppZihlLmtleT09PSJCYWNrc3BhY2UiKXsNCmRpZ2l0cz1kaWdpdHMuc2xpY2UoMCwtMSk7DQp1cGRhdGVDb3VudCgpOw0KfWVsc2UgaWYoZS5rZXk9PT0iRGVsZXRlInx8ZS5rZXk9PT0iRW50ZXIiKXsNCmRpZ2l0cz0iIjsNCnVwZGF0ZUNvdW50KCk7DQp9DQp9KTsNCg0KJCgic2VuZEJ0biIpLmFkZEV2"
    @"ZW50TGlzdGVuZXIoImNsaWNrIiwoKT0+ew0KY29uc3QgdmFsdWU9JCgibnVtYmVySW5wdXQiKS52YWx1ZS5yZXBsYWNlKC9bXjAtOV0vZywiIik7DQppZighdmFsdWUpcmV0dXJuIHNob3dUb2FzdCgi2YTYpyDYqtmI2KzYryDYo9ix2YLYp9mFINmE2KXYsdiz2KfZhNmH2KciKTsNCmRlbGl2ZXIodmFsdWUpOw0KfSk7DQoNCiQoImNsZWFyQnRuIikuYWRkRXZlbnRMaXN0ZW5lcigiY2xpY2siLCgpPT57DQpkaWdpdHM9IiI7DQokKCJudW1iZXJJbnB1dCIpLnZhbHVlPSIiOw0KdXBkYXRlQ291bnQoKTsNCn0pOw0KDQpyZW5kZXJQ"
    @"cmVzZXRzKCk7DQp1cGRhdGVTdGF0dXMoKTsNCjwvc2NyaXB0Pg0KPC9ib2R5Pg0KPC9odG1sPg0K";
    NSData *d = [[NSData alloc] initWithBase64EncodedString:b64 options:NSDataBase64DecodingIgnoreUnknownCharacters];
    return d ? [[NSString alloc] initWithData:d encoding:NSUTF8StringEncoding] : @"";
}


#pragma mark - نافذة شفافة تمرّر اللمس إلا فوق لوحتها (تستخدمها أدوات المنيو الصغيرة المستقلة)

@interface DSMiniWindow : UIWindow
@end
@implementation DSMiniWindow
- (UIView *)hitTest:(CGPoint)p withEvent:(UIEvent *)e {
    UIView *v = [super hitTest:p withEvent:e];
    return (v == self.rootViewController.view || v == self) ? nil : v;   // اللمس يمر للتطبيق إلا فوق اللوحة
}
@end

#pragma mark - الكتابة السريعة (منيو مستقل: تكتب رسالة واحدة فترسل لآخر حقل دردشة فتحته)

@interface DSQuickWindow : UIWindow
@end
@implementation DSQuickWindow
- (UIView *)hitTest:(CGPoint)p withEvent:(UIEvent *)e {
    UIView *v = [super hitTest:p withEvent:e];
    return (v == self.rootViewController.view || v == self) ? nil : v;
}
@end

// لا يستهدف إلا الحقل الذي كان المستخدم يكتب فيه فعلياً (gKbField) — رسالة واحدة، إرسال واحد يدوي، بدون أي تكرار أو جهات متعددة.
static BOOL DSQuickEligibleField(id t) {
    if (!t || ![NSThread isMainThread]) return NO;
    if (![t isKindOfClass:UITextField.class] && ![t isKindOfClass:UITextView.class]) return NO;
    UIView *v = (UIView *)t;
    if (!v.window || v.window.hidden) return NO;                       // الحقل لم يعد ظاهراً
    if ([v.window isKindOfClass:DSPassWindow.class]) return NO;         // ليس حقلاً من شاشات الأداة نفسها
    if ([v.window isKindOfClass:DSMiniWindow.class]) return NO;
    if ([v.window isKindOfClass:DSQuickWindow.class]) return NO;
    if ([(id<UITextInputTraits>)t isSecureTextEntry]) return NO;        // أبداً في حقل كلمة سر
    return YES;
}

// يستبدل كل محتوى الحقل المستهدف برسالتك ثم يرسل مرة واحدة (نفس محاكاة زر Return المستخدمة في باقي الأداة)
static BOOL DSQuickSendTo(id t, NSString *msg) {
    if (!DSQuickEligibleField(t) || !msg.length) return NO;
    id<UITextInput> ti = (id<UITextInput>)t;
    UITextRange *full = [ti textRangeFromPosition:ti.beginningOfDocument toPosition:ti.endOfDocument];
    if (full) [ti setSelectedTextRange:full];
    NSString *out = DSQuickModesOn() ? DSComposeMessage(msg) : msg;   // الأوضاع تُطبَّق مرة وحدة على الرسالة كاملة
    if (!out.length) out = msg;
    gKbBusy = YES;                 // لا تُشغّل خطط الكيبورد مرة ثانية على النص المُركَّب (تفادي التطبيق المزدوج)
    [(id)t insertText:out];
    gKbBusy = NO;
    DSKbSendNow(t);
    return YES;
}

static id DSQuickTarget(void) { return gKbField; }

@interface DSQuickVC : UIViewController <UITextFieldDelegate>
@end
@implementation DSQuickVC {
    UIView *_panel; UITextField *_input; UILabel *_status;
}

- (void)viewDidLoad {
    [super viewDidLoad];
    self.view.backgroundColor = UIColor.clearColor;
    self.overrideUserInterfaceStyle = UIUserInterfaceStyleDark;
    CGFloat W = 250, H = 150;
    CGRect sb = UIScreen.mainScreen.bounds;
    _panel = [[UIView alloc] initWithFrame:CGRectMake((sb.size.width - W) / 2, sb.size.height - H - 140, W, H)];
    _panel.backgroundColor = [DSHex(kPanel) colorWithAlphaComponent:0.97];
    _panel.layer.cornerRadius = 16; _panel.layer.cornerCurve = kCACornerCurveContinuous;
    _panel.layer.borderWidth = 1.3; _panel.layer.borderColor = [DSHex(kCyan) colorWithAlphaComponent:0.8].CGColor;
    DSGlow(_panel.layer, DSHex(kCyan), 10);
    [self.view addSubview:_panel];
    [_panel addGestureRecognizer:[[UIPanGestureRecognizer alloc] initWithTarget:self action:@selector(pan:)]];

    UILabel *title = [[UILabel alloc] initWithFrame:CGRectMake(10, 6, W - 48, 18)];
    title.text = @"📝 الكتابة السريعة"; title.textColor = DSHex(kCyan);
    title.font = [UIFont systemFontOfSize:12 weight:UIFontWeightHeavy]; title.adjustsFontSizeToFitWidth = YES; title.minimumScaleFactor = 0.7;
    [_panel addSubview:title];

    UIButton *close = [UIButton buttonWithType:UIButtonTypeCustom]; close.frame = CGRectMake(W - 32, 4, 24, 22);
    [close setTitle:@"✕" forState:UIControlStateNormal]; [close setTitleColor:DSHex(kRed) forState:UIControlStateNormal];
    close.titleLabel.font = [UIFont systemFontOfSize:13 weight:UIFontWeightHeavy];
    close.backgroundColor = [DSHex(kRed) colorWithAlphaComponent:0.14]; close.layer.cornerRadius = 7;
    [close addTarget:self action:@selector(closeTap) forControlEvents:UIControlEventTouchUpInside];
    [_panel addSubview:close];

    _status = [[UILabel alloc] initWithFrame:CGRectMake(10, 28, W - 20, 16)];
    _status.font = [UIFont systemFontOfSize:10.5 weight:UIFontWeightSemibold]; _status.textColor = DSHex(kDim);
    _status.text = @"يرسل لآخر حقل دردشة فتحته"; _status.adjustsFontSizeToFitWidth = YES; _status.minimumScaleFactor = 0.6;
    [_panel addSubview:_status];

    _input = [[UITextField alloc] initWithFrame:CGRectMake(10, 48, W - 20, 36)];
    _input.backgroundColor = [UIColor colorWithWhite:1 alpha:0.06]; _input.textColor = DSHex(kText);
    _input.font = [UIFont systemFontOfSize:13]; _input.layer.cornerRadius = 8;
    _input.leftView = [[UIView alloc] initWithFrame:CGRectMake(0, 0, 8, 1)]; _input.leftViewMode = UITextFieldViewModeAlways;
    _input.placeholder = @"اكتب رسالتك هنا…";
    _input.delegate = self;
    [_input addTarget:self action:@selector(inputChanged) forControlEvents:UIControlEventEditingChanged];
    _input.returnKeyType = UIReturnKeySend;
    [_panel addSubview:_input];

    UIButton *send = [UIButton buttonWithType:UIButtonTypeCustom]; send.frame = CGRectMake(10, 94, W - 20, 40);
    [send setTitle:@"⬆︎ إرسال" forState:UIControlStateNormal]; [send setTitleColor:DSHex(kGreen) forState:UIControlStateNormal];
    send.titleLabel.font = [UIFont systemFontOfSize:14 weight:UIFontWeightHeavy];
    send.backgroundColor = [DSHex(kGreen) colorWithAlphaComponent:0.14]; send.layer.cornerRadius = 9;
    send.layer.borderWidth = 1; send.layer.borderColor = [DSHex(kGreen) colorWithAlphaComponent:0.7].CGColor;
    [send addTarget:self action:@selector(sendTap) forControlEvents:UIControlEventTouchUpInside];
    [_panel addSubview:send];
}

- (void)inputChanged { if (DSDigitSendIsOn() && DSDigitComplete(_input.text)) [self sendTap]; }   // اكتمل عدد الأرقام ← أرسل

- (void)sendTap {
    NSString *msg = [_input.text stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceAndNewlineCharacterSet];
    if (!msg.length) return;
    __weak id target = gKbField;
    if (DSQuickSendTo(target, msg)) {
        _input.text = @"";
        // تأكيد حقيقي: يفحص هل تفرّغ حقل الدردشة فعلاً (ما تفعله كل تطبيقات الدردشة بعد إرسال ناجح)
        // بدون أي إعادة إرسال أو تكرار — فحص واحد فقط، لا يلمس الحقل. 0.00s: فوري بلا أي تأخير.
        [self confirmDeliveryOf:target];
    } else {
        _status.text = @"⚠️ افتح حقل الدردشة واضغط فيه أولاً"; _status.textColor = DSHex(kRed);
        [self performSelector:@selector(resetStatus) withObject:nil afterDelay:2.0];
    }
}

- (void)confirmDeliveryOf:(id)t {
    NSString *remaining = nil;
    if ([t isKindOfClass:UITextField.class]) remaining = ((UITextField *)t).text;
    else if ([t isKindOfClass:UITextView.class]) remaining = ((UITextView *)t).text;
    BOOL cleared = (remaining == nil) || (remaining.length == 0);   // الحقل تفرّغ = التطبيق استلم الإرسال
    if (cleared) { _status.text = @"✅ أُرسلت فعلاً"; _status.textColor = DSHex(kGreen); }
    else { _status.text = @"⚠️ لم تُرسل — الحقل لم يتفرّغ، تحقق يدوياً"; _status.textColor = DSHex(kRed); }
    [self performSelector:@selector(resetStatus) withObject:nil afterDelay:2.5];
}

- (void)resetStatus { _status.text = @"يرسل لآخر حقل دردشة فتحته"; _status.textColor = DSHex(kDim); }

- (BOOL)textFieldShouldReturn:(UITextField *)tf { [self sendTap]; return YES; }

- (void)closeTap {
    [DSSettings shared].quickSendOn = NO; [[DSSettings shared] save];
    DSQuickHide();
}

- (void)pan:(UIPanGestureRecognizer *)g {
    CGPoint t = [g translationInView:self.view];
    CGRect f = _panel.frame; CGRect sb = self.view.bounds;
    f.origin.x = MAX(4, MIN(sb.size.width - f.size.width - 4, f.origin.x + t.x));
    f.origin.y = MAX(40, MIN(sb.size.height - f.size.height - 4, f.origin.y + t.y));
    _panel.frame = f; [g setTranslation:CGPointZero inView:self.view];
}
@end

static DSQuickWindow *gQuickWin;

static void DSQuickShow(void) {
    if (gQuickWin) { gQuickWin.hidden = NO; return; }
    UIWindowScene *scene = nil;
    for (UIScene *sc in UIApplication.sharedApplication.connectedScenes) {
        if ([sc isKindOfClass:UIWindowScene.class] && sc.activationState == UISceneActivationStateForegroundActive) {
            scene = (UIWindowScene *)sc; break;
        }
    }
    DSQuickWindow *w = scene ? [[DSQuickWindow alloc] initWithWindowScene:scene]
                             : [[DSQuickWindow alloc] initWithFrame:UIScreen.mainScreen.bounds];
    w.windowLevel = UIWindowLevelAlert + 145;
    w.backgroundColor = UIColor.clearColor;
    w.rootViewController = [DSQuickVC new];
    w.hidden = NO;
    gQuickWin = w;
}

static void DSQuickHide(void) { gQuickWin.hidden = YES; gQuickWin = nil; }

#pragma mark - السرعة الحية: منيو صغير ثانٍ + التقاط مشغّلات الصوت العامة

// يتحكم بكل صوت أونلاين: Agora (محرك WSOLA أعلاه) + AVPlayer/AVAudioPlayer (مشغّلات التطبيق نفسها).
static NSHashTable *DSLiveTable(BOOL audioPlayers) {
    static NSHashTable *a, *b; static dispatch_once_t once;
    dispatch_once(&once, ^{ a = [NSHashTable weakObjectsHashTable]; b = [NSHashTable weakObjectsHashTable]; });
    return audioPlayers ? b : a;
}
static void DSLiveTrack(id p, BOOL audioPlayers) {
    NSHashTable *t = DSLiveTable(audioPlayers);
    @synchronized (t) { [t addObject:p]; }
}

// يطبّق السرعة الحالية (أو 1x عند الإيقاف) على المشغّلات التي تعمل الآن
static void DSLiveApplyMedia(void) {
    dispatch_async(dispatch_get_main_queue(), ^{
        float r = gLiveSpeedOn ? gLiveSpeed : 1.0f;
        NSArray *pl, *al;
        @synchronized (DSLiveTable(NO)) { pl = DSLiveTable(NO).allObjects; }
        @synchronized (DSLiveTable(YES)) { al = DSLiveTable(YES).allObjects; }
        for (AVPlayer *p in pl) if (p.rate != 0.0f) p.rate = r;
        for (AVAudioPlayer *p in al) {
            if (p == gJoinPlayer || !p.isPlaying) continue;
            p.enableRate = YES; p.rate = MIN(MAX(r, 0.5f), 2.0f);   // AVAudioPlayer يدعم حتى 2x فقط
        }
    });
}

%group DSLiveMediaHooks

%hook AVPlayer
- (void)setRate:(float)rate {
    if (gLiveSpeedOn && gLiveSpeed > 1.0f && rate == 1.0f) {   // التطبيق يطلب تشغيلاً عادياً → نبدّله بسرعتنا
        @try { self.currentItem.audioTimePitchAlgorithm = AVAudioTimePitchAlgorithmSpectral; } @catch (__unused NSException *e) {}
        DSLiveTrack(self, NO);
        rate = gLiveSpeed;
    }
    %orig(rate);
}
- (void)play {
    %orig;
    if (gLiveSpeedOn && gLiveSpeed > 1.0f) { DSLiveTrack(self, NO); self.rate = gLiveSpeed; }
}
%end

%hook AVAudioPlayer
- (BOOL)play {
    BOOL on = gLiveSpeedOn && self != gJoinPlayer;   // لا نلمس صوت الدخول الخاص بالأداة
    if (on) self.enableRate = YES;                  // لازم قبل التحضير
    BOOL r = %orig;
    if (on) { DSLiveTrack(self, YES); self.rate = MIN(MAX(gLiveSpeed, 0.5f), 2.0f); }
    return r;
}
%end

%end

@interface DSLiveWindow : UIWindow
@end
@implementation DSLiveWindow
- (UIView *)hitTest:(CGPoint)p withEvent:(UIEvent *)e {
    UIView *v = [super hitTest:p withEvent:e];
    return (v == self.rootViewController.view || v == self) ? nil : v;   // اللمس يمر للتطبيق إلا فوق اللوحة
}
@end

@interface DSLiveVC : UIViewController
@end
@implementation DSLiveVC {
    UIView *_panel; NSMutableArray<UIButton *> *_speedBtns; UIButton *_delayBtn, *_globalBtn; UILabel *_status; NSTimer *_timer;
}

static const float kLiveSpeeds[5] = {1.0f, 1.5f, 2.0f, 3.0f, 4.0f};
static const int kLiveDelays[9] = {0, 5, 10, 20, 30, 60, 300, 600, 1800};   // ثواني: 0.0 ... 30 دقيقة
static NSString *DSLiveDelayText(long s) {
    if (s <= 0) return @"0.0s";
    if (s < 60) return [NSString stringWithFormat:@"%lds", s];
    return [NSString stringWithFormat:@"%ld د", s / 60];
}
static NSString *DSLiveMsText(int ms) {
    if (ms >= 60000) return [NSString stringWithFormat:@"%.1f د", ms / 60000.0];
    return [NSString stringWithFormat:@"%.1f ث", ms / 1000.0];
}

- (UIButton *)btn:(NSString *)t size:(CGFloat)sz color:(UIColor *)c frame:(CGRect)f sel:(SEL)s {
    UIButton *b = [UIButton buttonWithType:UIButtonTypeCustom]; b.frame = f;
    [b setTitle:t forState:UIControlStateNormal]; [b setTitleColor:c forState:UIControlStateNormal];
    b.titleLabel.font = [UIFont systemFontOfSize:sz weight:UIFontWeightHeavy];
    b.titleLabel.adjustsFontSizeToFitWidth = YES; b.titleLabel.minimumScaleFactor = 0.7;
    b.backgroundColor = [c colorWithAlphaComponent:0.15];
    b.layer.cornerRadius = 9; b.layer.borderWidth = 1; b.layer.borderColor = [c colorWithAlphaComponent:0.7].CGColor;
    [b addTarget:self action:s forControlEvents:UIControlEventTouchUpInside];
    return b;
}

- (void)viewDidLoad {
    [super viewDidLoad];
    self.view.backgroundColor = UIColor.clearColor;
    self.overrideUserInterfaceStyle = UIUserInterfaceStyleDark;
    CGFloat W = 236, H = 192;
    CGRect sb = UIScreen.mainScreen.bounds;
    _panel = [[UIView alloc] initWithFrame:CGRectMake(12, MAX(60, sb.size.height / 2 - H / 2), W, H)];
    _panel.backgroundColor = [DSHex(kPanel) colorWithAlphaComponent:0.96];
    _panel.layer.cornerRadius = 16; _panel.layer.cornerCurve = kCACornerCurveContinuous;
    _panel.layer.borderWidth = 1.3; _panel.layer.borderColor = [DSHex(kPurple) colorWithAlphaComponent:0.85].CGColor;
    DSGlow(_panel.layer, DSHex(kPurple), 10);
    [self.view addSubview:_panel];
    [_panel addGestureRecognizer:[[UIPanGestureRecognizer alloc] initWithTarget:self action:@selector(pan:)]];

    UILabel *title = [[UILabel alloc] initWithFrame:CGRectMake(10, 6, W - 48, 18)];
    title.text = @"🎚️ السرعة الحية"; title.textColor = DSHex(kPurple);
    title.font = [UIFont systemFontOfSize:12 weight:UIFontWeightHeavy];
    [_panel addSubview:title];
    [_panel addSubview:[self btn:@"✕" size:12 color:DSHex(kRed) frame:CGRectMake(W - 32, 4, 24, 22) sel:@selector(closeTap)]];

    _speedBtns = [NSMutableArray array];
    for (int i = 0; i < 5; i++) {
        NSString *t = (kLiveSpeeds[i] == (int)kLiveSpeeds[i]) ? [NSString stringWithFormat:@"x%d", (int)kLiveSpeeds[i]]
                                                              : [NSString stringWithFormat:@"x%.1f", kLiveSpeeds[i]];
        UIButton *b = [self btn:t size:12 color:DSHex(kCyan) frame:CGRectMake(10 + i * 44, 30, 40, 34) sel:@selector(speedTap:)];
        b.tag = i; [_panel addSubview:b]; [_speedBtns addObject:b];
    }
    _delayBtn = [self btn:@"" size:11.5 color:DSHex(kAmber) frame:CGRectMake(10, 72, 104, 32) sel:@selector(delayTap)];
    [_panel addSubview:_delayBtn];
    [_panel addSubview:[self btn:@"● LIVE" size:12 color:DSHex(kGreen) frame:CGRectMake(W - 114, 72, 104, 32) sel:@selector(liveTap)]];

    _globalBtn = [self btn:@"" size:11 color:DSHex(kCyan) frame:CGRectMake(10, 110, W - 20, 30) sel:@selector(globalTap)];
    [_panel addSubview:_globalBtn];

    _status = [[UILabel alloc] initWithFrame:CGRectMake(10, 148, W - 20, 18)];
    _status.textAlignment = NSTextAlignmentCenter; _status.textColor = DSHex(kGreen);
    _status.font = DSMono(11, UIFontWeightBold); _status.adjustsFontSizeToFitWidth = YES; _status.minimumScaleFactor = 0.7;
    [_panel addSubview:_status];
    UILabel *hint = [[UILabel alloc] initWithFrame:CGRectMake(10, 168, W - 20, 22)];
    hint.text = @"يبقى متأخراً دائماً بالتأخير المختار ولا يرجع للبث.\nيشغّل مسرّعاً على دفعات. اضغط نفس السرعة لإعادة التجميع."; hint.numberOfLines = 2;
    hint.textAlignment = NSTextAlignmentCenter; hint.textColor = DSHex(kDim); hint.font = [UIFont systemFontOfSize:8.5];
    [_panel addSubview:hint];

    __weak typeof(self) ws = self;
    _timer = [NSTimer scheduledTimerWithTimeInterval:0.25 repeats:YES block:^(NSTimer *t) { [ws refresh]; }];
    [self refresh];
}

- (void)dealloc { [_timer invalidate]; }

- (void)refresh {
    DSSettings *st = [DSSettings shared];
    for (UIButton *b in _speedBtns) {
        BOOL on = fabsf(kLiveSpeeds[b.tag] - st.liveSpeed) < 0.01f;
        UIColor *c = on ? DSHex(kGreen) : DSHex(kCyan);
        [b setTitleColor:c forState:UIControlStateNormal];
        b.backgroundColor = [c colorWithAlphaComponent:on ? 0.30 : 0.12];
        b.layer.borderColor = [c colorWithAlphaComponent:on ? 1.0 : 0.5].CGColor;
    }
    [_delayBtn setTitle:[NSString stringWithFormat:@"⏱ تأخير %@", DSLiveDelayText((long)st.liveDelay)] forState:UIControlStateNormal];
    BOOL gl = st.liveGlobal;
    [_globalBtn setTitle:(gl ? @"🌐 كل الصوت (Zego وغيره): ON" : @"🌐 كل الصوت (Zego وغيره): OFF") forState:UIControlStateNormal];
    UIColor *gc = gl ? DSHex(kGreen) : DSHex(kDim);
    [_globalBtn setTitleColor:gc forState:UIControlStateNormal];
    _globalBtn.backgroundColor = [gc colorWithAlphaComponent:0.14]; _globalBtn.layer.borderColor = [gc colorWithAlphaComponent:0.7].CGColor;
    int mode = gLiveMode, a = gLiveA, b = gLiveB;
    if (mode == 1) { _status.text = [NSString stringWithFormat:@"⏳ تجميع %@ / %@", DSLiveMsText(a), DSLiveMsText(b)]; _status.textColor = DSHex(kAmber); }
    else if (mode == 2) { _status.text = [NSString stringWithFormat:@"🚀 لحاق x%g — فوق التأخير %@", (double)st.liveSpeed, DSLiveMsText(a)]; _status.textColor = DSHex(kPurple); }
    else { _status.text = @"🟢 مباشر"; _status.textColor = DSHex(kGreen); }
}

- (void)speedTap:(UIButton *)b {
    float s = kLiveSpeeds[b.tag];
    DSSettings *st = [DSSettings shared];
    BOOL same = fabsf(st.liveSpeed - s) < 0.01f;
    st.liveSpeed = s; [st save];       // save يحدّث gLiveSpeed
    if (same) gLiveRestartGen++;       // نفس الزر مرة ثانية = ابدأ تجميعاً ولحاقاً جديداً
    DSLiveApplyMedia();
    [self refresh];
}

- (void)delayTap {
    DSSettings *st = [DSSettings shared];
    int next = kLiveDelays[0];
    for (int i = 0; i < 9; i++) if (kLiveDelays[i] > st.liveDelay) { next = kLiveDelays[i]; break; }
    st.liveDelay = next; [st save];
    [self refresh];
}

- (void)globalTap {   // يبدّل بين معالجة Agora فقط ومعالجة المخرج النهائي (Zego وأي محرك)
    DSSettings *st = [DSSettings shared];
    st.liveGlobal = !st.liveGlobal; [st save];
    gLiveLiveGen++;
    [self refresh];
}

- (void)liveTap { gLiveLiveGen++; [self refresh]; }   // ارجع للبث الحي فوراً

- (void)closeTap {   // ✕: يوقف الخيار ويخفي المنيو ويرجع المشغّلات 1x
    DSSettings *st = [DSSettings shared]; st.liveSpeedOn = NO; [st save];
    gLiveLiveGen++;
    DSLiveApplyMedia();
    [[NSNotificationCenter defaultCenter] postNotificationName:DSLiveSettingNote object:nil];
    DSLiveHide();
}

- (void)pan:(UIPanGestureRecognizer *)g {
    CGPoint t = [g translationInView:self.view];
    CGRect f = _panel.frame; CGRect sb = self.view.bounds;
    f.origin.x = MAX(4, MIN(sb.size.width - f.size.width - 4, f.origin.x + t.x));
    f.origin.y = MAX(40, MIN(sb.size.height - f.size.height - 4, f.origin.y + t.y));
    _panel.frame = f; [g setTranslation:CGPointZero inView:self.view];
}
@end

static DSLiveWindow *gLiveWin;

static void DSLiveShow(void) {
    if (gLiveWin) { gLiveWin.hidden = NO; return; }
    UIWindowScene *scene = nil;
    for (UIScene *sc in UIApplication.sharedApplication.connectedScenes) {
        if ([sc isKindOfClass:UIWindowScene.class] && sc.activationState == UISceneActivationStateForegroundActive) {
            scene = (UIWindowScene *)sc; break;
        }
    }
    DSLiveWindow *w = scene ? [[DSLiveWindow alloc] initWithWindowScene:scene]
                            : [[DSLiveWindow alloc] initWithFrame:UIScreen.mainScreen.bounds];
    w.windowLevel = UIWindowLevelAlert + 155;   // مستقل عن القائمة الرئيسية: يبقى لو أغلقتها
    w.backgroundColor = UIColor.clearColor;
    w.rootViewController = [DSLiveVC new];
    w.hidden = NO;
    gLiveWin = w;
}

static void DSLiveHide(void) { gLiveWin.hidden = YES; gLiveWin = nil; }

#pragma mark - منيو تسريع اللعبة الصغير (مستقل)

@interface DSGSWindow : UIWindow
@end
@implementation DSGSWindow
- (UIView *)hitTest:(CGPoint)p withEvent:(UIEvent *)e {
    UIView *v = [super hitTest:p withEvent:e];
    return (v == self.rootViewController.view || v == self) ? nil : v;   // اللمس يمر للتطبيق إلا فوق اللوحة
}
@end

static const double kGSSpeeds[6] = {1.0, 1.5, 2.0, 3.0, 4.0, 600.0};

@interface DSGSVC : UIViewController
@end
@implementation DSGSVC {
    UIView *_panel; NSMutableArray<UIButton *> *_btns; UILabel *_status; NSTimer *_timer;
}

- (UIButton *)btn:(NSString *)t size:(CGFloat)sz color:(UIColor *)c frame:(CGRect)f sel:(SEL)s {
    UIButton *b = [UIButton buttonWithType:UIButtonTypeCustom]; b.frame = f;
    [b setTitle:t forState:UIControlStateNormal]; [b setTitleColor:c forState:UIControlStateNormal];
    b.titleLabel.font = [UIFont systemFontOfSize:sz weight:UIFontWeightHeavy];
    b.titleLabel.adjustsFontSizeToFitWidth = YES; b.titleLabel.minimumScaleFactor = 0.7;
    b.backgroundColor = [c colorWithAlphaComponent:0.15];
    b.layer.cornerRadius = 9; b.layer.borderWidth = 1; b.layer.borderColor = [c colorWithAlphaComponent:0.7].CGColor;
    [b addTarget:self action:s forControlEvents:UIControlEventTouchUpInside];
    return b;
}

- (void)viewDidLoad {
    [super viewDidLoad];
    self.view.backgroundColor = UIColor.clearColor;
    self.overrideUserInterfaceStyle = UIUserInterfaceStyleDark;
    CGFloat W = 236, H = 146;
    CGRect sb = UIScreen.mainScreen.bounds;
    _panel = [[UIView alloc] initWithFrame:CGRectMake(sb.size.width - W - 12, MAX(60, sb.size.height / 2 - H / 2), W, H)];
    _panel.backgroundColor = [DSHex(kPanel) colorWithAlphaComponent:0.96];
    _panel.layer.cornerRadius = 16; _panel.layer.cornerCurve = kCACornerCurveContinuous;
    _panel.layer.borderWidth = 1.3; _panel.layer.borderColor = [DSHex(kAmber) colorWithAlphaComponent:0.85].CGColor;
    DSGlow(_panel.layer, DSHex(kAmber), 10);
    [self.view addSubview:_panel];
    [_panel addGestureRecognizer:[[UIPanGestureRecognizer alloc] initWithTarget:self action:@selector(pan:)]];

    UILabel *title = [[UILabel alloc] initWithFrame:CGRectMake(10, 6, W - 48, 18)];
    title.text = @"⏩ تسريع اللعبة (X8)"; title.textColor = DSHex(kAmber);
    title.font = [UIFont systemFontOfSize:12 weight:UIFontWeightHeavy];
    [_panel addSubview:title];
    [_panel addSubview:[self btn:@"✕" size:12 color:DSHex(kRed) frame:CGRectMake(W - 32, 4, 24, 22) sel:@selector(closeTap)]];

    _btns = [NSMutableArray array];
    for (int i = 0; i < 6; i++) {
        NSString *t = (kGSSpeeds[i] == (int)kGSSpeeds[i]) ? [NSString stringWithFormat:@"x%d", (int)kGSSpeeds[i]]
                                                          : [NSString stringWithFormat:@"x%.1f", kGSSpeeds[i]];
        CGRect fr = (i < 5) ? CGRectMake(10 + i * 44, 30, 40, 34)       // الصف الأول: x1 ... x4
                            : CGRectMake(10, 68, W - 20, 30);            // الصف الثاني: x600 (سرعة قصوى)
        UIButton *b = [self btn:(i < 5 ? t : @"x600  ⚠ سرعة قصوى") size:12 color:DSHex(kCyan) frame:fr sel:@selector(speedTap:)];
        b.tag = i; [_panel addSubview:b]; [_btns addObject:b];
    }

    _status = [[UILabel alloc] initWithFrame:CGRectMake(10, 102, W - 20, 18)];
    _status.textAlignment = NSTextAlignmentCenter; _status.textColor = DSHex(kGreen);
    _status.font = DSMono(11, UIFontWeightBold); _status.adjustsFontSizeToFitWidth = YES; _status.minimumScaleFactor = 0.7;
    [_panel addSubview:_status];
    UILabel *hint = [[UILabel alloc] initWithFrame:CGRectMake(10, 120, W - 20, 22)];
    hint.text = @"يسرّع ساعة التطبيق فقط (الصوت والاتصال خارج التسريع).\nيبدأ دائماً من x1 عند فتح التطبيق."; hint.numberOfLines = 2;
    hint.textAlignment = NSTextAlignmentCenter; hint.textColor = DSHex(kDim); hint.font = [UIFont systemFontOfSize:8.5];
    [_panel addSubview:hint];

    __weak typeof(self) ws = self;
    _timer = [NSTimer scheduledTimerWithTimeInterval:0.5 repeats:YES block:^(NSTimer *t) { [ws refresh]; DSGSApplyLayerSpeed(); }];
    [self refresh];
}

- (void)dealloc { [_timer invalidate]; }

- (void)refresh {
    double cur = DSGSGetScale();
    for (UIButton *b in _btns) {
        BOOL on = fabs(kGSSpeeds[b.tag] - cur) < 0.01;
        UIColor *c = on ? DSHex(kGreen) : DSHex(kCyan);
        [b setTitleColor:c forState:UIControlStateNormal];
        b.backgroundColor = [c colorWithAlphaComponent:on ? 0.30 : 0.12];
        b.layer.borderColor = [c colorWithAlphaComponent:on ? 1.0 : 0.5].CGColor;
    }
    if (cur == 1.0) { _status.text = @"🟢 عادي x1"; _status.textColor = DSHex(kGreen); }
    else { _status.text = [NSString stringWithFormat:@"🚀 تسريع x%g", cur]; _status.textColor = DSHex(kAmber); }
}

- (void)speedTap:(UIButton *)b {
    DSGSSetScale(kGSSpeeds[b.tag]);
    DSGSApplyLayerSpeed();
    [[NSNotificationCenter defaultCenter] postNotificationName:DSGSSettingNote object:nil];
    [self refresh];
}

- (void)closeTap {   // ✕: يوقف الخيار ويخفي المنيو ويرجع x1
    [NSUserDefaults.standardUserDefaults setBool:NO forKey:@"DSGameSpeedOn"];
    DSGSSetScale(1.0); DSGSApplyLayerSpeed();
    [[NSNotificationCenter defaultCenter] postNotificationName:DSGSSettingNote object:nil];
    DSGSHide();
}

- (void)pan:(UIPanGestureRecognizer *)g {
    CGPoint t = [g translationInView:self.view];
    CGRect f = _panel.frame; CGRect sb = self.view.bounds;
    f.origin.x = MAX(4, MIN(sb.size.width - f.size.width - 4, f.origin.x + t.x));
    f.origin.y = MAX(40, MIN(sb.size.height - f.size.height - 4, f.origin.y + t.y));
    _panel.frame = f; [g setTranslation:CGPointZero inView:self.view];
}
@end

static DSGSWindow *gGSWin;

static void DSGSShow(void) {
    if (gGSWin) { gGSWin.hidden = NO; return; }
    UIWindowScene *scene = nil;
    for (UIScene *sc in UIApplication.sharedApplication.connectedScenes) {
        if ([sc isKindOfClass:UIWindowScene.class] && sc.activationState == UISceneActivationStateForegroundActive) {
            scene = (UIWindowScene *)sc; break;
        }
    }
    DSGSWindow *w = scene ? [[DSGSWindow alloc] initWithWindowScene:scene]
                          : [[DSGSWindow alloc] initWithFrame:UIScreen.mainScreen.bounds];
    w.windowLevel = UIWindowLevelAlert + 156;   // مستقل عن القائمة الرئيسية: يبقى لو أغلقتها
    w.backgroundColor = UIColor.clearColor;
    w.rootViewController = [DSGSVC new];
    w.hidden = NO;
    gGSWin = w;
}

static void DSGSHide(void) { gGSWin.hidden = YES; gGSWin = nil; }

#pragma mark - الدول: علم في الشات → يكتب اسم الدولة أو العاصمة (زر عائم مستقل)

// 0 = إيقاف، 1 = اسم الدولة، 2 = العاصمة
static int  gFlagMode   = 0;
static BOOL gFlagSend   = NO;    // إرسال تلقائي بعد الكتابة
static BOOL gFlagStrict = YES;   // YES: الرسالة لازم تكون أعلاماً فقط (علم أو أكثر). NO: أي نص فيه علم

static void DSFlagLoad(void) {
    NSUserDefaults *d = NSUserDefaults.standardUserDefaults;
    [d registerDefaults:@{ @"DSFlagBubble": @YES, @"DSFlagStrict": @YES }];
    gFlagMode = (int)[d integerForKey:@"DSFlagMode"];
    if (gFlagMode < 0 || gFlagMode > 2) gFlagMode = 0;
    gFlagSend = [d boolForKey:@"DSFlagSend"];
    gFlagStrict = [d boolForKey:@"DSFlagStrict"];
}
static void DSFlagSave(void) {
    NSUserDefaults *d = NSUserDefaults.standardUserDefaults;
    [d setInteger:gFlagMode forKey:@"DSFlagMode"];
    [d setBool:gFlagSend forKey:@"DSFlagSend"];
    [d setBool:gFlagStrict forKey:@"DSFlagStrict"];
}

// الكود|الاسم|العاصمة
static NSDictionary<NSString *, NSArray<NSString *> *> *DSFlagTable(void) {
    static NSDictionary *d; static dispatch_once_t once;
    dispatch_once(&once, ^{
        NSString *raw =
        @"AF|أفغانستان|كابول\nAL|ألبانيا|تيرانا\nDZ|الجزائر|الجزائر\nAD|أندورا|أندورا لا فيلا\nAO|أنغولا|لواندا\n"
        @"AG|أنتيغوا وبربودا|سانت جونز\nAR|الأرجنتين|بوينس آيرس\nAM|أرمينيا|يريفان\nAU|أستراليا|كانبرا\nAT|النمسا|فيينا\n"
        @"AZ|أذربيجان|باكو\nBS|الباهاما|ناسو\nBH|البحرين|المنامة\nBD|بنغلاديش|دكا\nBB|بربادوس|بريدجتاون\n"
        @"BY|بيلاروسيا|مينسك\nBE|بلجيكا|بروكسل\nBZ|بليز|بلموبان\nBJ|بنين|بورتو نوفو\nBT|بوتان|تيمفو\n"
        @"BO|بوليفيا|سوكري\nBA|البوسنة والهرسك|سراييفو\nBW|بوتسوانا|غابورون\nBR|البرازيل|برازيليا\nBN|بروناي|بندر سيري بيغاوان\n"
        @"BG|بلغاريا|صوفيا\nBF|بوركينا فاسو|واغادوغو\nBI|بوروندي|جيتيغا\nKH|كمبوديا|بنوم بنه\nCM|الكاميرون|ياوندي\n"
        @"CA|كندا|أوتاوا\nCV|الرأس الأخضر|برايا\nCF|أفريقيا الوسطى|بانغي\nTD|تشاد|إنجامينا\nCL|تشيلي|سانتياغو\n"
        @"CN|الصين|بكين\nCO|كولومبيا|بوغوتا\nKM|جزر القمر|موروني\nCG|الكونغو|برازافيل\nCD|الكونغو الديمقراطية|كينشاسا\n"
        @"CR|كوستاريكا|سان خوسيه\nCI|ساحل العاج|ياموسوكرو\nHR|كرواتيا|زغرب\nCU|كوبا|هافانا\nCY|قبرص|نيقوسيا\n"
        @"CZ|التشيك|براغ\nDK|الدنمارك|كوبنهاغن\nDJ|جيبوتي|جيبوتي\nDM|دومينيكا|روسو\nDO|الدومينيكان|سانتو دومينغو\n"
        @"EC|الإكوادور|كيتو\nEG|مصر|القاهرة\nSV|السلفادور|سان سلفادور\nGQ|غينيا الاستوائية|مالابو\nER|إريتريا|أسمرة\n"
        @"EE|إستونيا|تالين\nSZ|إسواتيني|مبابان\nET|إثيوبيا|أديس أبابا\nFJ|فيجي|سوفا\nFI|فنلندا|هلسنكي\n"
        @"FR|فرنسا|باريس\nGA|الغابون|ليبرفيل\nGM|غامبيا|بانجول\nGE|جورجيا|تبليسي\nDE|ألمانيا|برلين\n"
        @"GH|غانا|أكرا\nGR|اليونان|أثينا\nGD|غرينادا|سانت جورجز\nGT|غواتيمالا|غواتيمالا\nGN|غينيا|كوناكري\n"
        @"GW|غينيا بيساو|بيساو\nGY|غيانا|جورج تاون\nHT|هايتي|بورت أو برنس\nHN|هندوراس|تيغوسيغالبا\nHU|المجر|بودابست\n"
        @"IS|آيسلندا|ريكيافيك\nIN|الهند|نيودلهي\nID|إندونيسيا|جاكرتا\nIR|إيران|طهران\nIQ|العراق|بغداد\n"
        @"IE|أيرلندا|دبلن\nIT|إيطاليا|روما\nJM|جامايكا|كينغستون\nJP|اليابان|طوكيو\nJO|الأردن|عمّان\n"
        @"KZ|كازاخستان|أستانا\nKE|كينيا|نيروبي\nKI|كيريباتي|تاراوا\nKW|الكويت|الكويت\nKG|قيرغيزستان|بيشكيك\n"
        @"LA|لاوس|فيينتيان\nLV|لاتفيا|ريغا\nLB|لبنان|بيروت\nLS|ليسوتو|ماسيرو\nLR|ليبيريا|مونروفيا\n"
        @"LY|ليبيا|طرابلس\nLI|ليختنشتاين|فادوز\nLT|ليتوانيا|فيلنيوس\nLU|لوكسمبورغ|لوكسمبورغ\nMG|مدغشقر|أنتاناناريفو\n"
        @"MW|مالاوي|ليلونغوي\nMY|ماليزيا|كوالالمبور\nMV|المالديف|ماليه\nML|مالي|باماكو\nMT|مالطا|فاليتا\n"
        @"MH|جزر مارشال|ماجورو\nMR|موريتانيا|نواكشوط\nMU|موريشيوس|بورت لويس\nMX|المكسيك|مكسيكو سيتي\nFM|ميكرونيزيا|باليكير\n"
        @"MD|مولدوفا|كيشيناو\nMC|موناكو|موناكو\nMN|منغوليا|أولان باتور\nME|الجبل الأسود|بودغوريتسا\nMA|المغرب|الرباط\n"
        @"MZ|موزمبيق|مابوتو\nMM|ميانمار|نايبيداو\nNA|ناميبيا|ويندهوك\nNR|ناورو|يارين\nNP|نيبال|كاتماندو\n"
        @"NL|هولندا|أمستردام\nNZ|نيوزيلندا|ويلنغتون\nNI|نيكاراغوا|ماناغوا\nNE|النيجر|نيامي\nNG|نيجيريا|أبوجا\n"
        @"KP|كوريا الشمالية|بيونغ يانغ\nMK|مقدونيا الشمالية|سكوبيه\nNO|النرويج|أوسلو\nOM|عُمان|مسقط\nPK|باكستان|إسلام آباد\n"
        @"PW|بالاو|نغيرولمود\nPS|فلسطين|القدس\nPA|بنما|بنما\nPG|بابوا غينيا الجديدة|بورت مورسبي\nPY|باراغواي|أسونسيون\n"
        @"PE|بيرو|ليما\nPH|الفلبين|مانيلا\nPL|بولندا|وارسو\nPT|البرتغال|لشبونة\nQA|قطر|الدوحة\n"
        @"RO|رومانيا|بوخارست\nRU|روسيا|موسكو\nRW|رواندا|كيغالي\nKN|سانت كيتس ونيفيس|باسيتير\nLC|سانت لوسيا|كاستريس\n"
        @"VC|سانت فنسنت والغرينادين|كينغستاون\nWS|ساموا|أبيا\nSM|سان مارينو|سان مارينو\nST|ساو تومي وبرينسيبي|ساو تومي\nSA|السعودية|الرياض\n"
        @"SN|السنغال|داكار\nRS|صربيا|بلغراد\nSC|سيشل|فيكتوريا\nSL|سيراليون|فريتاون\nSG|سنغافورة|سنغافورة\n"
        @"SK|سلوفاكيا|براتيسلافا\nSI|سلوفينيا|ليوبليانا\nSB|جزر سليمان|هونيارا\nSO|الصومال|مقديشو\nZA|جنوب أفريقيا|بريتوريا\n"
        @"KR|كوريا الجنوبية|سيول\nSS|جنوب السودان|جوبا\nES|إسبانيا|مدريد\nLK|سريلانكا|كولومبو\nSD|السودان|الخرطوم\n"
        @"SR|سورينام|باراماريبو\nSE|السويد|ستوكهولم\nCH|سويسرا|برن\nSY|سوريا|دمشق\nTW|تايوان|تايبيه\n"
        @"TJ|طاجيكستان|دوشانبي\nTZ|تنزانيا|دودوما\nTH|تايلاند|بانكوك\nTL|تيمور الشرقية|ديلي\nTG|توغو|لومي\n"
        @"TO|تونغا|نوكو ألوفا\nTT|ترينيداد وتوباغو|بورت أوف سبين\nTN|تونس|تونس\nTR|تركيا|أنقرة\nTM|تركمانستان|عشق آباد\n"
        @"TV|توفالو|فونافوتي\nUG|أوغندا|كمبالا\nUA|أوكرانيا|كييف\nAE|الإمارات|أبوظبي\nGB|بريطانيا|لندن\n"
        @"US|أمريكا|واشنطن\nUY|الأوروغواي|مونتيفيديو\nUZ|أوزبكستان|طشقند\nVU|فانواتو|بورت فيلا\nVA|الفاتيكان|الفاتيكان\n"
        @"VE|فنزويلا|كاراكاس\nVN|فيتنام|هانوي\nYE|اليمن|صنعاء\nZM|زامبيا|لوساكا\nZW|زيمبابوي|هراري\nXK|كوسوفو|بريشتينا";
        NSMutableDictionary *m = [NSMutableDictionary dictionary];
        for (NSString *line in [raw componentsSeparatedByString:@"\n"]) {
            NSArray *p = [line componentsSeparatedByString:@"|"];
            if (p.count == 3) m[p[0]] = @[p[1], p[2]];
        }
        d = m;
    });
    return d;
}

// يستخرج كل الأعلام من النص (علم أو أكثر). strict: لا يقبل إلا أعلاماً وفواصل/مسافات.
static NSArray<NSString *> *DSFlagCodes(NSString *s, BOOL strict) {
    NSUInteger n = s.length;
    if (n < 4 || n > 240) return nil;
    NSMutableArray *codes = [NSMutableArray array];
    NSCharacterSet *ws = NSCharacterSet.whitespaceAndNewlineCharacterSet;
    NSUInteger i = 0;
    while (i < n) {
        unichar a = [s characterAtIndex:i];
        if (a == 0xD83C && i + 3 < n) {
            unichar b = [s characterAtIndex:i + 1], c = [s characterAtIndex:i + 2], d = [s characterAtIndex:i + 3];
            if (b >= 0xDDE6 && b <= 0xDDFF && c == 0xD83C && d >= 0xDDE6 && d <= 0xDDFF) {
                unichar cc[2] = { (unichar)('A' + (b - 0xDDE6)), (unichar)('A' + (d - 0xDDE6)) };
                [codes addObject:[NSString stringWithCharacters:cc length:2]];
                if (codes.count >= 12) break;
                i += 4; continue;
            }
        }
        if (strict) {
            BOOL ok = [ws characterIsMember:a] || a == 0xFE0F || a == 0x200B || a == 0x200E || a == 0x200F
                   || a == ',' || a == 0x060C || a == '-' || a == '.' || a == '/' || a == '|';
            if (!ok) return nil;
        }
        i++;
    }
    return codes.count ? codes : nil;
}

// الحقل المفتوح الآن (الكيبورد الظاهر)
static __weak id gFlagGrabbed;
@interface UIResponder (DSFlag)
- (void)dsFlagGrab;
@end
@implementation UIResponder (DSFlag)
- (void)dsFlagGrab { gFlagGrabbed = self; }
@end

// يكتب النص فوراً بدل محتوى الحقل (بدون تدخل تكرار الأرقام/تفكيك الحروف)
static void DSFlagType(NSString *msg) {
    gFlagGrabbed = nil;
    [UIApplication.sharedApplication sendAction:@selector(dsFlagGrab) to:nil from:nil forEvent:nil];
    id t = gFlagGrabbed;
    if (!DSQuickEligibleField(t)) t = gKbField;        // آخر حقل كتبت فيه
    if (!DSQuickEligibleField(t)) return;              // ما في كيبورد مفتوح
    id<UITextInput> ti = (id<UITextInput>)t;
    UITextRange *full = [ti textRangeFromPosition:ti.beginningOfDocument toPosition:ti.endOfDocument];
    if (full) [ti setSelectedTextRange:full];
    gKbBusy = YES;
    [(id)t insertText:msg];
    gKbBusy = NO;
    if (gFlagSend) DSKbSendNow(t);
}

static NSString *gFlagLastKey; static CFAbsoluteTime gFlagLastT;

static void DSFlagScan(NSString *s, UIView *v) {
    if (!gFlagMode || ![s isKindOfClass:NSString.class] || s.length < 4) return;   // رفض سريع
    if (![NSThread isMainThread]) { dispatch_async(dispatch_get_main_queue(), ^{ DSFlagScan(s, v); }); return; }
    UIWindow *w = v.window;
    if (w && ([w isKindOfClass:DSPassWindow.class] || [w isKindOfClass:DSMiniWindow.class]
           || [w isKindOfClass:DSQuickWindow.class] || [w isKindOfClass:DSLiveWindow.class] || [NSStringFromClass(w.class) isEqualToString:@"DSFlagWindow"])) return;
    NSArray<NSString *> *codes = DSFlagCodes(s, gFlagStrict);
    if (!codes) return;
    CFAbsoluteTime now = CFAbsoluteTimeGetCurrent();
    if ([s isEqualToString:gFlagLastKey] && now - gFlagLastT < 1.2) return;       // نفس الرسالة (إعادة رسم)
    gFlagLastKey = [s copy]; gFlagLastT = now;
    NSDictionary *tb = DSFlagTable();
    NSMutableArray *ans = [NSMutableArray array];
    for (NSString *c in codes) { NSArray *e = tb[c]; if (e) [ans addObject:e[gFlagMode == 1 ? 0 : 1]]; }
    if (!ans.count) return;
    DSFlagType([ans componentsJoinedByString:@" "]);                              // كل الأعلام بالترتيب، مفصولة بمسافة
}

%group DSFlagHooks

%hook UILabel
- (void)setText:(NSString *)t { %orig; DSFlagScan(t, self); }
- (void)setAttributedText:(NSAttributedString *)t { %orig; DSFlagScan(t.string, self); }
%end

%hook UITextView
- (void)setText:(NSString *)t { %orig; DSFlagScan(t, self); }
- (void)setAttributedText:(NSAttributedString *)t { %orig; DSFlagScan(t.string, self); }
%end

%end

@interface DSFlagWindow : UIWindow
@end
@implementation DSFlagWindow
- (UIView *)hitTest:(CGPoint)p withEvent:(UIEvent *)e {
    UIView *v = [super hitTest:p withEvent:e];
    return (v == self.rootViewController.view || v == self) ? nil : v;   // اللمس يمر للعبة إلا فوق الزر واللوحة
}
@end

@interface DSFlagVC : UIViewController
@end
@implementation DSFlagVC {
    UIView *_panel; UIButton *_bubble, *_nameBtn, *_capBtn, *_offBtn, *_sendBtn, *_strictBtn; UILabel *_status;
}

- (UIButton *)btn:(NSString *)t size:(CGFloat)sz color:(UIColor *)c frame:(CGRect)f sel:(SEL)s {
    UIButton *b = [UIButton buttonWithType:UIButtonTypeCustom]; b.frame = f;
    [b setTitle:t forState:UIControlStateNormal]; [b setTitleColor:c forState:UIControlStateNormal];
    b.titleLabel.font = [UIFont systemFontOfSize:sz weight:UIFontWeightHeavy];
    b.titleLabel.adjustsFontSizeToFitWidth = YES; b.titleLabel.minimumScaleFactor = 0.7;
    b.backgroundColor = [c colorWithAlphaComponent:0.15];
    b.layer.cornerRadius = 9; b.layer.borderWidth = 1; b.layer.borderColor = [c colorWithAlphaComponent:0.7].CGColor;
    [b addTarget:self action:s forControlEvents:UIControlEventTouchUpInside];
    return b;
}

- (void)viewDidLoad {
    [super viewDidLoad];
    self.view.backgroundColor = UIColor.clearColor;
    self.overrideUserInterfaceStyle = UIUserInterfaceStyleDark;
    CGRect sb = UIScreen.mainScreen.bounds;

    // الزر العائم الصغير 🚩
    _bubble = [UIButton buttonWithType:UIButtonTypeCustom];
    _bubble.frame = CGRectMake(sb.size.width - 58, sb.size.height / 2 + 40, 46, 46);
    _bubble.backgroundColor = [DSHex(kPanel) colorWithAlphaComponent:0.95];
    _bubble.layer.cornerRadius = 23; _bubble.layer.borderWidth = 2;
    [_bubble setTitle:@"🚩" forState:UIControlStateNormal];
    _bubble.titleLabel.font = [UIFont systemFontOfSize:22];
    [_bubble addTarget:self action:@selector(bubbleTap) forControlEvents:UIControlEventTouchUpInside];
    [_bubble addGestureRecognizer:[[UIPanGestureRecognizer alloc] initWithTarget:self action:@selector(bubblePan:)]];
    [self.view addSubview:_bubble];

    // اللوحة الصغيرة (تظهر عند الضغط على الزر)
    CGFloat W = 232, H = 150;
    _panel = [[UIView alloc] initWithFrame:CGRectMake(0, 0, W, H)];
    _panel.backgroundColor = [DSHex(kPanel) colorWithAlphaComponent:0.97];
    _panel.layer.cornerRadius = 16; _panel.layer.cornerCurve = kCACornerCurveContinuous;
    _panel.layer.borderWidth = 1.3; _panel.layer.borderColor = [DSHex(kGreen) colorWithAlphaComponent:0.85].CGColor;
    DSGlow(_panel.layer, DSHex(kGreen), 10);
    _panel.hidden = YES;
    [self.view addSubview:_panel];

    UILabel *title = [[UILabel alloc] initWithFrame:CGRectMake(10, 6, W - 48, 18)];
    title.text = @"🚩 الدول"; title.textColor = DSHex(kGreen);
    title.font = [UIFont systemFontOfSize:12 weight:UIFontWeightHeavy];
    [_panel addSubview:title];
    [_panel addSubview:[self btn:@"✕" size:12 color:DSHex(kRed) frame:CGRectMake(W - 32, 4, 24, 22) sel:@selector(bubbleTap)]];

    _nameBtn = [self btn:@"🌍 اسم الدولة" size:12 color:DSHex(kCyan) frame:CGRectMake(10, 30, 104, 34) sel:@selector(nameTap)];
    _capBtn  = [self btn:@"🏛 العاصمة" size:12 color:DSHex(kCyan) frame:CGRectMake(W - 114, 30, 104, 34) sel:@selector(capTap)];
    _offBtn  = [self btn:@"⏹ إيقاف" size:11.5 color:DSHex(kRed) frame:CGRectMake(10, 70, 104, 30) sel:@selector(offTap)];
    _sendBtn = [self btn:@"" size:11 color:DSHex(kAmber) frame:CGRectMake(W - 114, 70, 104, 30) sel:@selector(sendTap)];
    _strictBtn = [self btn:@"" size:10.5 color:DSHex(kPurple) frame:CGRectMake(10, 106, W - 20, 28) sel:@selector(strictTap)];
    for (UIView *v in @[_nameBtn, _capBtn, _offBtn, _sendBtn, _strictBtn]) [_panel addSubview:v];

    _status = [[UILabel alloc] initWithFrame:CGRectMake(10, 134, W - 20, 14)];
    _status.textAlignment = NSTextAlignmentCenter; _status.font = DSMono(10, UIFontWeightBold);
    _status.adjustsFontSizeToFitWidth = YES; _status.minimumScaleFactor = 0.7;
    [_panel addSubview:_status];
    [self refresh];
}

- (void)refresh {
    UIColor *on = DSHex(kGreen), *off = DSHex(kCyan);
    for (UIButton *b in @[_nameBtn, _capBtn]) {
        BOOL a = (b == _nameBtn) ? gFlagMode == 1 : gFlagMode == 2;
        UIColor *c = a ? on : off;
        [b setTitleColor:c forState:UIControlStateNormal];
        b.backgroundColor = [c colorWithAlphaComponent:a ? 0.30 : 0.12];
        b.layer.borderColor = [c colorWithAlphaComponent:a ? 1.0 : 0.5].CGColor;
    }
    [_sendBtn setTitle:(gFlagSend ? @"⬆︎ إرسال: ON" : @"⬆︎ إرسال: OFF") forState:UIControlStateNormal];
    [_strictBtn setTitle:(gFlagStrict ? @"الرسالة: أعلام فقط (اضغط للتبديل)" : @"الرسالة: أي نص فيه علم (اضغط للتبديل)") forState:UIControlStateNormal];
    _status.text = gFlagMode == 1 ? @"🟢 يكتب اسم الدولة" : (gFlagMode == 2 ? @"🟢 يكتب العاصمة" : @"⚪️ متوقف");
    _status.textColor = gFlagMode ? DSHex(kGreen) : DSHex(kDim);
    UIColor *bc = gFlagMode ? DSHex(kGreen) : DSHex(kDim);
    _bubble.layer.borderColor = bc.CGColor;
    DSGlow(_bubble.layer, bc, gFlagMode ? 8 : 0);
}

- (void)layoutPanel {
    CGRect sb = self.view.bounds, b = _bubble.frame;
    CGFloat W = _panel.bounds.size.width, H = _panel.bounds.size.height;
    CGFloat x = MAX(4, MIN(sb.size.width - W - 4, b.origin.x + b.size.width - W));
    CGFloat y = b.origin.y + b.size.height + 6;
    if (y + H > sb.size.height - 4) y = b.origin.y - H - 6;
    _panel.frame = CGRectMake(x, MAX(30, y), W, H);
}

- (void)bubbleTap { _panel.hidden = !_panel.hidden; if (!_panel.hidden) [self layoutPanel]; }

- (void)bubblePan:(UIPanGestureRecognizer *)g {
    CGPoint t = [g translationInView:self.view];
    CGRect f = _bubble.frame, sb = self.view.bounds;
    f.origin.x = MAX(2, MIN(sb.size.width - f.size.width - 2, f.origin.x + t.x));
    f.origin.y = MAX(30, MIN(sb.size.height - f.size.height - 2, f.origin.y + t.y));
    _bubble.frame = f; [g setTranslation:CGPointZero inView:self.view];
    if (!_panel.hidden) [self layoutPanel];
}

- (void)nameTap   { gFlagMode = (gFlagMode == 1) ? 0 : 1; DSFlagSave(); [self refresh]; }
- (void)capTap    { gFlagMode = (gFlagMode == 2) ? 0 : 2; DSFlagSave(); [self refresh]; }
- (void)offTap    { gFlagMode = 0; DSFlagSave(); [self refresh]; }
- (void)sendTap   { gFlagSend = !gFlagSend; DSFlagSave(); [self refresh]; }
- (void)strictTap { gFlagStrict = !gFlagStrict; DSFlagSave(); [self refresh]; }
@end

static DSFlagWindow *gFlagWin;

static void DSFlagShow(void) {
    if (gFlagWin) { gFlagWin.hidden = NO; return; }
    UIWindowScene *scene = nil;
    for (UIScene *sc in UIApplication.sharedApplication.connectedScenes) {
        if ([sc isKindOfClass:UIWindowScene.class] && sc.activationState == UISceneActivationStateForegroundActive) {
            scene = (UIWindowScene *)sc; break;
        }
    }
    DSFlagWindow *w = scene ? [[DSFlagWindow alloc] initWithWindowScene:scene]
                            : [[DSFlagWindow alloc] initWithFrame:UIScreen.mainScreen.bounds];
    w.windowLevel = UIWindowLevelAlert + 160;   // مستقل عن القائمة الرئيسية
    w.backgroundColor = UIColor.clearColor;
    w.rootViewController = [DSFlagVC new];
    w.hidden = NO;
    gFlagWin = w;
}
static void DSFlagHide(void) { gFlagWin.hidden = YES; gFlagWin = nil; }

static BOOL DSFlagBubbleIsOn(void) { return [NSUserDefaults.standardUserDefaults boolForKey:@"DSFlagBubble"]; }
static void DSFlagSetBubble(BOOL on) {
    [NSUserDefaults.standardUserDefaults setBool:on forKey:@"DSFlagBubble"];
    if (on) DSFlagShow(); else DSFlagHide();
}

#pragma mark - PING على الشاشة
// يقيس زمن مصافحة TCP (SYN ← SYN-ACK أو RST) نحو هدف، وهو أقرب شي لـ ping العادي بدون صلاحيات ICMP.
static double DSPingProbe(uint32_t ipBE, uint16_t portBE, double timeoutSec) {
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return -1;
    int fl = fcntl(fd, F_GETFL, 0); fcntl(fd, F_SETFL, fl | O_NONBLOCK);
    int one = 1; setsockopt(fd, SOL_SOCKET, SO_NOSIGPIPE, &one, sizeof one);
    struct sockaddr_in sa; memset(&sa, 0, sizeof sa);
    sa.sin_len = sizeof sa; sa.sin_family = AF_INET; sa.sin_addr.s_addr = ipBE; sa.sin_port = portBE;
    double t0 = DSNow(), ms = -1;
    int rc = (orig_connect ? orig_connect : connect)(fd, (struct sockaddr *)&sa, sizeof sa);   // مباشرة بدون hook الأداة
    if (rc == 0) ms = (DSNow() - t0) * 1000.0;
    else if (errno == EINPROGRESS) {
        struct pollfd p = { fd, POLLOUT, 0 };
        if (poll(&p, 1, (int)(timeoutSec * 1000)) > 0) {
            int err = 0; socklen_t el = sizeof err;
            getsockopt(fd, SOL_SOCKET, SO_ERROR, &err, &el);
            if (err == 0 || err == ECONNREFUSED) ms = (DSNow() - t0) * 1000.0;   // الرفض = وصل رد من الطرف الآخر = زمن الذهاب والإياب
        }
    }
    close(fd);
    return ms;
}

static BOOL DSPingResolveTarget(NSInteger t, uint32_t *ip, uint16_t *port, NSString **name) {
    if (t == 2 && gPingGameIP) {
        *ip = gPingGameIP; *port = gPingGamePort;
        struct in_addr a; a.s_addr = gPingGameIP; char buf[INET_ADDRSTRLEN] = {0}; inet_ntop(AF_INET, &a, buf, sizeof buf);
        *name = [NSString stringWithFormat:@"GAME %s", buf];
        return YES;
    }
    if (t == 1) { *ip = htonl(0x08080808); *port = htons(443); *name = @"Google 8.8.8.8"; return YES; }
    *ip = htonl(0x01010101); *port = htons(443);
    *name = (t == 2) ? @"GAME ؟ (لا سيرفر بعد) → CF" : @"Cloudflare 1.1.1.1";
    return YES;
}

@interface DSPingWindow : UIWindow
@end
@implementation DSPingWindow
- (UIView *)hitTest:(CGPoint)p withEvent:(UIEvent *)e {
    UIView *v = [super hitTest:p withEvent:e];
    return (v == self.rootViewController.view || v == self) ? nil : v;   // اللمس يمر للتطبيق إلا فوق الشارة
}
@end

@interface DSPingVC : UIViewController
@end
@implementation DSPingVC {
    UIView *_pill; UILabel *_val, *_sub; NSTimer *_timer; BOOL _busy, _placed;
}

- (void)viewDidLoad {
    [super viewDidLoad];
    self.view.backgroundColor = UIColor.clearColor;
    self.overrideUserInterfaceStyle = UIUserInterfaceStyleDark;
    _pill = [[UIView alloc] initWithFrame:CGRectMake(0, 0, 150, 40)];
    _pill.backgroundColor = [UIColor colorWithWhite:0.05 alpha:0.78];
    _pill.layer.cornerRadius = 12; _pill.layer.cornerCurve = kCACornerCurveContinuous;
    _pill.layer.borderWidth = 1.2; _pill.layer.borderColor = [UIColor colorWithWhite:0.6 alpha:0.8].CGColor;
    [self.view addSubview:_pill];
    _val = [[UILabel alloc] initWithFrame:CGRectMake(6, 3, 138, 20)];
    _val.textAlignment = NSTextAlignmentCenter; _val.textColor = UIColor.whiteColor;
    _val.font = [UIFont monospacedDigitSystemFontOfSize:15 weight:UIFontWeightHeavy];
    [_pill addSubview:_val];
    _sub = [[UILabel alloc] initWithFrame:CGRectMake(6, 22, 138, 14)];
    _sub.textAlignment = NSTextAlignmentCenter; _sub.textColor = [UIColor colorWithWhite:0.75 alpha:1];
    _sub.font = [UIFont systemFontOfSize:9 weight:UIFontWeightSemibold];
    _sub.adjustsFontSizeToFitWidth = YES; _sub.minimumScaleFactor = 0.7;
    [_pill addSubview:_sub];
    [_pill addGestureRecognizer:[[UITapGestureRecognizer alloc] initWithTarget:self action:@selector(tapTarget)]];
    [_pill addGestureRecognizer:[[UIPanGestureRecognizer alloc] initWithTarget:self action:@selector(pan:)]];
    _val.text = @"PING …"; [self refreshName];
    __weak typeof(self) ws = self;
    _timer = [NSTimer scheduledTimerWithTimeInterval:1.5 repeats:YES block:^(NSTimer *t) { [ws tick]; }];
    [self tick];
}

- (void)viewDidLayoutSubviews {
    [super viewDidLayoutSubviews];
    if (_placed || self.view.bounds.size.width < 10) return;
    _placed = YES;
    CGFloat top = MAX(self.view.safeAreaInsets.top, 20) + 2;
    _pill.frame = CGRectMake((self.view.bounds.size.width - 150) / 2, top, 150, 40);
}

- (void)dealloc { [_timer invalidate]; }

- (void)refreshName {
    uint32_t ip; uint16_t pt; NSString *nm = @"";
    DSPingResolveTarget(gPingTarget, &ip, &pt, &nm);
    _sub.text = nm;
}

- (void)tick {
    if (_busy || !gPingOn) return;
    _busy = YES;
    uint32_t ip; uint16_t pt; NSString *nm = @"";
    DSPingResolveTarget(gPingTarget, &ip, &pt, &nm);
    _sub.text = nm;
    __weak typeof(self) ws = self;
    dispatch_async(dispatch_get_global_queue(QOS_CLASS_USER_INITIATED, 0), ^{
        double ms = DSPingProbe(ip, pt, 2.0);
        dispatch_async(dispatch_get_main_queue(), ^{ [ws showMs:ms]; });
    });
}

- (void)showMs:(double)ms {
    _busy = NO;
    UIColor *c;
    if (ms < 0) { _val.text = @"PING —"; c = [UIColor colorWithRed:0.95 green:0.25 blue:0.25 alpha:1]; }
    else {
        _val.text = [NSString stringWithFormat:@"PING %.0f ms", ms];
        c = ms < 60 ? [UIColor colorWithRed:0.2 green:0.85 blue:0.4 alpha:1]
          : ms < 120 ? [UIColor colorWithRed:1 green:0.75 blue:0.2 alpha:1]
                     : [UIColor colorWithRed:0.95 green:0.3 blue:0.3 alpha:1];
    }
    _val.textColor = c; _pill.layer.borderColor = c.CGColor;
}

- (void)tapTarget {   // الضغط على الشارة يبدّل الهدف: Cloudflare ← Google ← سيرفر اللعبة
    DSSettings *st = [DSSettings shared];
    st.pingTarget = (st.pingTarget + 1) % 3; [st save];
    _val.text = @"PING …";
    [self refreshName];
    _busy = NO; [self tick];
}

- (void)pan:(UIPanGestureRecognizer *)g {
    CGPoint t = [g translationInView:self.view];
    CGRect f = _pill.frame, b = self.view.bounds;
    f.origin.x = MAX(2, MIN(b.size.width - f.size.width - 2, f.origin.x + t.x));
    f.origin.y = MAX(20, MIN(b.size.height - f.size.height - 2, f.origin.y + t.y));
    _pill.frame = f; [g setTranslation:CGPointZero inView:self.view];
}
@end

static DSPingWindow *gPingWin;

static void DSPingShow(void) {
    if (gPingWin) { gPingWin.hidden = NO; return; }
    UIWindowScene *scene = nil;
    for (UIScene *sc in UIApplication.sharedApplication.connectedScenes) {
        if ([sc isKindOfClass:UIWindowScene.class] && sc.activationState == UISceneActivationStateForegroundActive) { scene = (UIWindowScene *)sc; break; }
    }
    DSPingWindow *w = scene ? [[DSPingWindow alloc] initWithWindowScene:scene]
                            : [[DSPingWindow alloc] initWithFrame:UIScreen.mainScreen.bounds];
    w.windowLevel = UIWindowLevelAlert + 160;   // فوق كل شي، ومستقل عن القائمة الرئيسية
    w.backgroundColor = UIColor.clearColor;
    w.rootViewController = [DSPingVC new];
    w.hidden = NO;
    gPingWin = w;
}

static void DSPingHide(void) { gPingWin.hidden = YES; gPingWin = nil; }

static DSPassWindow *gWindow;

static void DSShow(void) {
    if (gWindow) return;
    UIWindowScene *scene = nil;
    for (UIScene *s in UIApplication.sharedApplication.connectedScenes) {
        if ([s isKindOfClass:UIWindowScene.class] && s.activationState == UISceneActivationStateForegroundActive) {
            scene = (UIWindowScene *)s; break;
        }
    }
    DSPassWindow *w = scene ? [[DSPassWindow alloc] initWithWindowScene:scene]
                            : [[DSPassWindow alloc] initWithFrame:UIScreen.mainScreen.bounds];
    w.windowLevel = UIWindowLevelAlert + 100;
    w.backgroundColor = UIColor.clearColor;
    w.rootViewController = [DSRootVC new];
    w.hidden = NO;
    gWindow = w;
}

__attribute__((constructor)) static void DSInit(void) {
    @autoreleasepool {
        [DSStore shared];
        [DSSettings shared];  // يحمّل القواعد المفعّلة فوراً قبل أي اتصال
        [DSProxy shared];     // يحمّل البروكسي المحفوظ قبل أي اتصال
        DSAudioBoot();        // تقوية الصوت + QoS + مخزن الجهاز (الحالة المحفوظة)
        DSInstallCHooks();
        DSInstallURLSessionHooks();
        [[ASTestManager shared] start];      // AUTO TEST: يبدأ فوراً عند تفعيل ALL/CHAT
        [[STAutoManager shared] start];       // مجدول اختبار الضغط التلقائي (AUTO LOAD)
        %init(DSAgoraJoinSoundHooks);
        %init(DSLiveMediaHooks);   // السرعة الحية: AVPlayer / AVAudioPlayer
        DSFlagLoad();
        if (DSAgoraLowLat() >= 5) DSZegoApplyConfig();   // Zego يقرأ إعداداته عند التهيئة، فنرسلها مبكراً
        %init(DSFlagHooks);       // الدول: علم في الشات → اسم/عاصمة
        %init(DSKeyboardHooks);   // الكيبورد: تكرار الأرقام / تفكيك الحروف
        DSKbInstallFrameObservers();   // مكان الكيبورد (لحساسية اللمس)
        [[NSNotificationCenter defaultCenter] addObserverForName:UIApplicationDidBecomeActiveNotification object:nil
            queue:NSOperationQueue.mainQueue usingBlock:^(NSNotification *n) {
            dispatch_after(dispatch_time(DISPATCH_TIME_NOW, 1 * NSEC_PER_SEC), dispatch_get_main_queue(), ^{ DSShow(); if ([DSSettings shared].pingOn) DSPingShow(); if ([DSSettings shared].quickSendOn) DSQuickShow(); if ([DSSettings shared].liveSpeedOn) DSLiveShow(); if ([NSUserDefaults.standardUserDefaults boolForKey:@"DSGameSpeedOn"]) DSGSShow(); if (DSFlagBubbleIsOn()) DSFlagShow(); });
        }];
    }
}
