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
n = 0
for page in site.rglob('*.html'):
    t = page.read_text(encoding='utf-8')
    if '</head>' not in t: continue
    rel = os.path.relpath(site, page.parent)
    add = ''
    if 'serre.css' not in t: add += f'<link rel="stylesheet" href="{rel}/serre.css">\n'
    if 'serre.js' not in t: add += f'<script defer src="{rel}/serre.js"></script>\n'
    if not add: continue
    page.write_text(t.replace('</head>', add + '</head>', 1), encoding='utf-8')
    n += 1
print(f'{n} pages styled')
