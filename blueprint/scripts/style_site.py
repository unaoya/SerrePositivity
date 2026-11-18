#!/usr/bin/env python3
"""生成済みのブループリントのサイトに、SerrePositivity の見た目（blueprint/style/serre.css）を読み込ませる。

使い方: python3 blueprint/scripts/style_site.py <サイトのディレクトリ>
  serre.css をサイトの根に写し、各 index.html の <head> の末尾に相対の <link> を足す（既にあれば足さない）。
  Verso の出力は変えない。lake exe vbp build の後に毎回かける。
"""
import pathlib, shutil, sys, os
site = pathlib.Path(sys.argv[1]).resolve()
css = pathlib.Path(__file__).resolve().parents[1] / 'style' / 'serre.css'
shutil.copy(css, site / 'serre.css')
n = 0
for page in site.rglob('*.html'):
    t = page.read_text(encoding='utf-8')
    if 'serre.css' in t or '</head>' not in t: continue
    rel = os.path.relpath(site / 'serre.css', page.parent)
    page.write_text(t.replace('</head>', f'<link rel="stylesheet" href="{rel}">\n</head>', 1), encoding='utf-8')
    n += 1
print(f'{n} pages styled')
