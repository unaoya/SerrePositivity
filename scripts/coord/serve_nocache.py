"""ブループリントのプレビューの配信（127.0.0.1:8790、Cache-Control: no-store）。使い方：python3 scripts/coord/serve_nocache.py <サイトのディレクトリ>"""
import http.server, functools, sys
class H(http.server.SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header('Cache-Control', 'no-store'); super().end_headers()
http.server.ThreadingHTTPServer(('127.0.0.1', 8790), functools.partial(H, directory=sys.argv[1])).serve_forever()
