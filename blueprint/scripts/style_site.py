#!/usr/bin/env python3
"""生成済みのブループリントのサイトに、SerrePositivity の見た目（blueprint/style/serre.css）を読み込ませる。

使い方: python3 blueprint/scripts/style_site.py <サイトのディレクトリ>
  serre.css・serre.js をサイトの根に写し、各 index.html の <head> の末尾に相対の <link>・<script> を足す（既にあれば足さない）。
  Verso の出力は変えない。lake exe vbp build の後に毎回かける。
"""
import pathlib, shutil, sys, os
site = pathlib.Path(sys.argv[1]).resolve()
css = pathlib.Path(__file__).resolve().parents[1] / 'style' / 'serre.css'
shutil.copy(css, site / 'serre.css')
shutil.copy(css.with_name('serre.js'), site / 'serre.js')
# 目次の木：各章のページの二つ目の目次（その章の節の一覧）から、章 → 節の表を作る（serre.js が全体の目次に差し込む）
import re, json, html
tree = {}
for page in site.glob('*/index.html'):
    t = page.read_text(encoding='utf-8')
    i = t.find('<nav id="toc">'); j = t.find('</nav>', i)
    blocks = t[i:j].split('<div class="split-toc">')[1:2]
    if not blocks: continue
    links = re.findall(r'<a href="([^"]*)"[^>]*>(.*?)</a>', blocks[0], flags=re.S)
    if len(links) < 2: continue
    key = links[0][0].split('#')[0]
    tree[key] = [[h, html.unescape(re.sub(r'<[^>]+>', '', s)).strip()] for h, s in links[1:]]
(site / 'serre-toc.js').write_text('window.SP_TOC = ' + json.dumps(tree, ensure_ascii=False) + ';\n', encoding='utf-8')
print(f'{len(tree)} chapters with sections')
import re, time
VER = int(time.time())
n = 0
for page in site.rglob('*.html'):
    t = page.read_text(encoding='utf-8')
    if '</head>' not in t: continue
    rel = os.path.relpath(site, page.parent)
    # 既に足してあれば入れ替える。?v=… はブラウザに古い CSS・JS を使わせないため（http.server は期限を付けないので、ブラウザが推定で持ち続ける）
    t = re.sub(r'<link rel="stylesheet" href="[^"]*serre\.css[^"]*">\n|<script defer src="[^"]*serre(?:-toc)?\.js[^"]*"></script>\n', '', t)
    add = (f'<link rel="stylesheet" href="{rel}/serre.css?v={VER}">\n'
           f'<script defer src="{rel}/serre-toc.js?v={VER}"></script>\n'
           f'<script defer src="{rel}/serre.js?v={VER}"></script>\n')
    page.write_text(t.replace('</head>', add + '</head>', 1), encoding='utf-8')
    n += 1
print(f'{n} pages styled')
