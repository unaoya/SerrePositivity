"""対応表の地図のページ（HTML）を、リポジトリの中で作り直すための道具（2026-11-17）。
各地図は research/<文献>-coverage/map/ に
  template.html … ページの見た目と動き（データの部分は {{DATA}}）
  data.json     … ページに埋め込むデータ
を置き、build で index.html を作る（index.html は生成物なので git に入れない）。
正本は対応表（review/*.csv）。data.json の状態・宣言・理由は refresh で対応表から作り直す。

使い方（リポジトリの root で）：
  python3 scripts/docs/coverage_map.py split <公開中のページの HTML> <map のディレクトリ>
  python3 scripts/docs/coverage_map.py build <map のディレクトリ>
  python3 scripts/docs/coverage_map.py refresh <map のディレクトリ> <review のディレクトリ> --format kerodon|ha|htt
公開は Artifact（URL は各 map/README.md）へ index.html を出す。"""
import sys, re, json, csv, glob, os
MARK = '{{DATA}}'
PAT = re.compile(r'(<script id="data" type="application/json">)(.*?)(</script>)', re.S)
def split(src, d):
    s = open(src, encoding='utf-8').read()
    i = s.find('<title>')
    if i > 0: s = s[i:]                       # 公開の仕組みが前に足す <head> を外す
    if s.rstrip().endswith('</body></html>'): s = s.rstrip()[:-len('</body></html>')]
    m = PAT.search(s)
    data = json.loads(m.group(2))
    os.makedirs(d, exist_ok=True)
    open(f'{d}/template.html', 'w', encoding='utf-8').write(s[:m.start(2)] + MARK + s[m.end(2):])
    json.dump(data, open(f'{d}/data.json', 'w', encoding='utf-8'), ensure_ascii=False, indent=0)
    print('split', src, '->', d, 'items', len(data.get('items', [])))
def build(d):
    t = open(f'{d}/template.html', encoding='utf-8').read()
    data = json.load(open(f'{d}/data.json', encoding='utf-8'))
    js = json.dumps(data, ensure_ascii=False, separators=(',', ':')).replace('</', '<\\/')
    open(f'{d}/index.html', 'w', encoding='utf-8').write(t.replace(MARK, js, 1))
    print('built', f'{d}/index.html')
COLS = {'kerodon': ('status_new', 'declarations_new', 'reason'), 'ha': ('status', 'declarations', 'reason'), 'htt': ('status', 'declarations', 'reason')}
def refresh(d, review, fmt):
    st, dc, rs = COLS[fmt]
    rev = {}
    for f in glob.glob(f'{review}/*.csv'):
        for r in csv.DictReader(open(f, encoding='utf-8')): rev[r['number']] = r
    data = json.load(open(f'{d}/data.json', encoding='utf-8'))
    n = 0
    for it in data['items']:          # 配列の形：[番号, 種類, 状態, 宣言, 理由, ...]
        r = rev.get(it[0])
        if not r: continue
        new = [it[0], it[1], r[st], [[e.split(' @ ', 1)[0].strip(), e.split(' @ ', 1)[1].strip() if ' @ ' in e else ''] for e in r[dc].split(' | ') if e.strip()], r[rs]]
        if it[2:5] != new[2:5]: n += 1
        it[2:5] = new[2:5]
    json.dump(data, open(f'{d}/data.json', 'w', encoding='utf-8'), ensure_ascii=False, indent=0)
    print('refreshed', n, 'items from', review)
if __name__ == '__main__':
    a = sys.argv[1:]
    if a[0] == 'split': split(a[1], a[2])
    elif a[0] == 'build': build(a[1])
    elif a[0] == 'refresh': refresh(a[1], a[2], a[a.index('--format') + 1])
    else: print(__doc__)
