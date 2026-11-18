#!/usr/bin/env python3
"""生成済みのブループリントのサイトに、SerrePositivity の見た目（blueprint/style/serre.css）を読み込ませる。

使い方: python3 blueprint/scripts/style_site.py <サイトのディレクトリ>
  serre.css・serre.js をサイトの根に写し、各 index.html の <head> の末尾に相対の <link>・<script> を足す（既にあれば足さない）。
  lake exe vbp build の後に毎回かける。Verso の出力で書き換えるのは、依存グラフの節点の色（対応表の状態が一部・未証明の入力に依存のもの、末尾）だけ。
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

# 依存グラフ：対応表の状態が「一部」「未証明の入力に依存」の節点の色を変える（11-18）。
# Verso はグラフの節点の見た目（visual）を JSON でページに埋めているので、それを書き換える。状態は生成した章（SerreBlueprint/**/*.lean）の
# 「:::種類 "ラベル"」の次の行（「対応表の状態：…。」）から読む。
status = {}
src = pathlib.Path(__file__).resolve().parents[1] / 'SerreBlueprint'
for f in src.rglob('*.lean'):
    lab = None
    for l in f.read_text(encoding='utf-8').split('\n'):
        m = re.match(r':::\w+ "([^"]+)"', l)
        if m: lab = m.group(1); continue
        if lab:
            m = re.search(r'対応表の状態：([^。]*)。', l)
            if m: status[lab] = 'partial' if m.group(1).startswith('一部') else 'interface' if m.group(1).startswith('未証明の入力') else ''
            lab = None
VIS = {'partial': dict(color='#b7791f', fillcolor='#fdf3dc', fontcolor='#5f370e', tip='対応表：一部（原典どおりではない）'),
       'interface': dict(color='#b91c1c', fillcolor='#fde8e8', fontcolor='#7f1d1d', tip='対応表：未証明の入力に依存')}
LEGEND = ('<span class="bp_graph_legend_item sp-legend"><span class="bp_graph_legend_swatch" style="background: #fdf3dc; border-color: #b7791f; border-width: 1px; border-style: solid; border-radius: 0.2rem"></span>一部（原典どおりではない）</span>'
          '<span class="bp_graph_legend_item sp-legend"><span class="bp_graph_legend_swatch" style="background: #fde8e8; border-color: #b91c1c; border-width: 1px; border-style: solid; border-radius: 0.2rem"></span>未証明の入力に依存</span>')
g = 0
for page in site.rglob('*.html'):
    t = page.read_text(encoding='utf-8')
    if 'class="bp-graph-data"' not in t: continue
    def fix(m):
        global g
        d = json.loads(m.group(2)); c = 0
        for n in d.get('nodes', []):
            v = VIS.get(status.get(n.get('label'), ''))
            if not v or 'visual' not in n: continue
            n['visual'].update(color=v['color'], fillcolor=v['fillcolor'], fontcolor=v['fontcolor'], style='filled')
            tip = n['visual'].get('tooltip', '')
            if v['tip'] not in tip: n['visual']['tooltip'] = (tip + ' | ' if tip else '') + v['tip']
            c += 1
        g += c
        return m.group(1) + json.dumps(d, ensure_ascii=False).replace('</', '<\\/') + m.group(3)
    t2 = re.sub(r'(<script type="application/json" class="bp-graph-data">)(.*?)(</script>)', fix, t, flags=re.S)
    if 'sp-legend' not in t2:
        t2 = t2.replace('<span class="bp_graph_legend_item">Solid:', LEGEND + '<span class="bp_graph_legend_item">Solid:', 1)
    if t2 != t: page.write_text(t2, encoding='utf-8')
print(f'{g} graph nodes recoloured ({sum(1 for v in status.values() if v)} partial/interface labels)')
