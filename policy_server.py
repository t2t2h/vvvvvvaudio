#!/usr/bin/env python3
"""خادم سياسة بسيط لـ AflatoonSuite (مكتبة بايثون القياسية فقط).

الاستخدام:
    export POLICY_KEY='نفس المفتاح اللي حطيته بالأداة'
    python3 policy_server.py --port 8080 --file policy.json
ضعه خلف HTTPS (Cloudflare Tunnel / Caddy / nginx) لأن الأداة ترفض http.
عدّل policy.json وارفع "gen" لتصل التغييرات (الأداة ترفض gen أقدم أو مساوٍ للمطبّق).
"""
import argparse, hashlib, hmac, json, os, sys
from http.server import BaseHTTPRequestHandler, HTTPServer
from urllib.parse import urlparse, parse_qs

class H(BaseHTTPRequestHandler):
    key = b""; file = "policy.json"
    def do_GET(self):
        u = urlparse(self.path)
        if u.path != "/api/v1/policy":
            self.send_response(404); self.end_headers(); return
        q = parse_qs(u.query)
        sys.stderr.write("sync device=%s build=%s\n" % (q.get("device", ["?"])[0], q.get("build", ["?"])[0]))
        try:
            body = open(self.file, "rb").read()
            json.loads(body)                     # لازم JSON صالح
        except Exception as e:
            self.send_response(500); self.end_headers(); self.wfile.write(str(e).encode()); return
        sig = hmac.new(self.key, body, hashlib.sha256).hexdigest()
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("X-Signature", sig)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers(); self.wfile.write(body)
    def log_message(self, *a): pass

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", type=int, default=8080); ap.add_argument("--file", default="policy.json")
    ap.add_argument("--host", default="127.0.0.1")
    a = ap.parse_args()
    k = os.environ.get("POLICY_KEY", "")
    if not k: sys.exit("حدّد POLICY_KEY بمتغير البيئة")
    H.key = k.encode("utf-8"); H.file = a.file
    print("policy server on %s:%d  (file=%s)" % (a.host, a.port, a.file))
    HTTPServer((a.host, a.port), H).serve_forever()
