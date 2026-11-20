"""概念の木のページ（HTML）を作る。使い方：python3 page.py <trunk-…-sub.csv> <出力.html> <版の名前>"""
import csv, sys, html, collections
rows = list(csv.DictReader(open(sys.argv[1], encoding='utf-8'))); OUT = sys.argv[2]; VER = sys.argv[3]
I = lambda r, k: int(r[k]); e = html.escape
G = collections.OrderedDict()
for r in rows: G.setdefault(r['group'], collections.OrderedDict()).setdefault(r['concept'], []).append(r)
def agg(rs):
    c = collections.Counter()
    for r in rs:
        for k in ['decls', 'lines', 'layer1', 'layer2', 'layer3', 'layer4', '言い換え', '未使用']: c[k] += I(r, k)
    return c
TOT = agg(rows); MAXC = max(agg(rs)['decls'] for g in G.values() for rs in g.values())
def kind(s):
    if s == '（まだ読んでいない定義）': return 'unread', '未読'
    if s.startswith('（補助）'): return 'aux', '補助'
    if s.startswith('（読んで移') or s.startswith('（行き先'): return 'moved', '移動'
    if s.startswith('（'): return 'other', '未分類'
    return 'read', ''
def nums(c, bar=None):
    p = lambda a: f'{c[a] / c["decls"] * 100:.0f}%' if c['decls'] else '–'
    b = f'<span class="bar"><i style="width:{max(1, c["decls"] / bar * 100):.1f}%"></i></span>' if bar else '<span class="bar"></span>'
    return f'<span class="n">{c["decls"]:,}</span>{b}<span class="n dim">{c["lines"]:,}</span><span class="n">{c["layer1"]:,}</span><span class="n dim">{p("言い換え")}</span><span class="n dim">{p("未使用")}</span>'
H = []
for g, cs in G.items():
    gc = agg([r for rs in cs.values() for r in rs])
    H.append(f'<details class="g" open><summary><span class="t">{e(g)}</span>{nums(gc)}</summary>')
    for cn, rs in sorted(cs.items(), key=lambda kv: -agg(kv[1])['decls']):
        cc = agg(rs); named = [r for r in rs if kind(r['subconcept'])[0] in ('read', 'aux')]
        if len(rs) == 1 and not named:
            H.append(f'<div class="c leaf"><span class="t">{e(cn)}</span>{nums(cc, MAXC)}</div>'); continue
        H.append(f'<details class="c"><summary><span class="t">{e(cn)}<small>{len(named)} 小概念</small></span>{nums(cc, MAXC)}</summary><div class="subs">')
        for r in sorted(rs, key=lambda r: (kind(r['subconcept'])[0] not in ('read',), kind(r['subconcept'])[0] != 'aux', -I(r, 'decls'))):
            k, lab = kind(r['subconcept']); sc = agg([r])
            tag = f'<b class="tag {k}">{lab}</b>' if lab else ''
            nm = r['subconcept'].replace('（補助）', '') if k == 'aux' else r['subconcept']
            d = f'<span class="d">{e(r["description"])}{(" <cite>" + e(r["reference"]) + "</cite>") if r["reference"] else ""}</span>' if r['description'] or r['reference'] else ''
            H.append(f'<div class="s {k}"><span class="t">{tag}{e(nm)}{d}</span>{nums(sc, cc["decls"])}</div>')
        H.append('</div></details>')
    H.append('</details>')
st = collections.Counter()
for r in rows: st[kind(r['subconcept'])[0]] += I(r, 'decls')
page = f'''<title>SerrePositivity 概念の木</title>
<meta name="claude:viewport-fit-sides" content="cover">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Noto+Sans+JP:wght@400;500;700&family=IBM+Plex+Mono:wght@400;500&display=swap">
<style>
/* layout: one outline column; each row = name on the left, a fixed grid of figures on the right; three levels by indentation */
:root {{ --bg:#fbfbf9; --fg:#1d2327; --dim:#6a7378; --line:#e1e4e2; --band:#f1f3f1; --accent:#1f6f6b; --aux:#a4671b; --unread:#8a8f93; --moved:#6a5aa8;
  --sans:"Noto Sans JP","Hiragino Sans","Yu Gothic",system-ui,sans-serif; --mono:"IBM Plex Mono",ui-monospace,Menlo,monospace }}
@media (prefers-color-scheme: dark) {{ :root:not([data-theme="light"]) {{ --bg:#15191b; --fg:#e4e8e7; --dim:#98a2a5; --line:#2b3235; --band:#1d2326; --accent:#5fc2bb; --aux:#e0a458; --unread:#8c9599; --moved:#a99be6; color-scheme:dark }} }}
:root[data-theme="dark"] {{ --bg:#15191b; --fg:#e4e8e7; --dim:#98a2a5; --line:#2b3235; --band:#1d2326; --accent:#5fc2bb; --aux:#e0a458; --unread:#8c9599; --moved:#a99be6; color-scheme:dark }}
body {{ background:var(--bg); color:var(--fg); font:14px/1.6 var(--sans); padding-block:28px 60px; padding-left:max(16px,env(safe-area-inset-left,0px)); padding-right:max(16px,env(safe-area-inset-right,0px)) }}
main {{ max-width:1080px; margin:0 auto; display:flex; flex-direction:column; gap:20px }}
h1 {{ font-size:22px; font-weight:700; margin:0; text-wrap:balance }}
p {{ margin:0; max-width:68ch; color:var(--dim) }} p b {{ color:var(--fg); font-weight:500 }}
.facts {{ display:flex; flex-wrap:wrap; gap:8px 28px; font-size:13px; color:var(--dim) }} .facts b {{ font:500 15px var(--mono); color:var(--fg); margin-right:4px }}
.tree {{ overflow-x:auto }} .inner {{ min-width:720px }}
.head, summary, .leaf, .s {{ display:grid; grid-template-columns:minmax(0,1fr) 64px 90px 84px 60px 52px 52px; gap:10px; align-items:baseline }}
.head {{ font-size:11px; letter-spacing:.04em; color:var(--dim); border-bottom:1px solid var(--line); padding:0 6px 6px }} .head span:not(:first-child) {{ text-align:right }} .head span:nth-child(3) {{ text-align:left }}
summary {{ cursor:pointer; list-style:none; padding:5px 6px; border-radius:4px }} summary::-webkit-details-marker {{ display:none }}
summary:hover, .leaf:hover, .s:hover {{ background:var(--band) }} summary:focus-visible {{ outline:2px solid var(--accent); outline-offset:1px }}
.t {{ min-width:0 }} summary .t::before {{ content:"▸"; display:inline-block; width:1.1em; color:var(--dim) }} details[open] > summary .t::before {{ content:"▾" }}
.g > summary {{ font-weight:700; font-size:15px; border-bottom:1px solid var(--line); margin-top:14px }}
.c > summary, .leaf {{ padding-left:22px }} .leaf {{ padding-block:5px; padding-right:6px; border-radius:4px }} .leaf .t {{ padding-left:1.1em }}
.t small {{ color:var(--dim); font-size:11px; margin-left:8px; font-weight:400 }}
.subs {{ margin:2px 0 8px 40px; border-left:2px solid var(--line); padding-left:10px }}
.s {{ padding:4px 6px; border-radius:4px; font-size:13px }} .s .d {{ display:block; color:var(--dim); font-size:12px; line-height:1.5 }} cite {{ font-style:normal; color:var(--accent) }}
.s.unread .t, .s.other .t, .s.moved .t {{ color:var(--dim) }}
.tag {{ font:500 10px var(--sans); border:1px solid currentColor; border-radius:3px; padding:0 4px; margin-right:6px; vertical-align:1px }} .tag.aux {{ color:var(--aux) }} .tag.unread, .tag.other {{ color:var(--unread) }} .tag.moved {{ color:var(--moved) }}
.n {{ font:400 12.5px var(--mono); font-variant-numeric:tabular-nums; text-align:right }} .dim {{ color:var(--dim) }}
.bar {{ display:block; height:6px; align-self:center; background:transparent }} .bar i {{ display:block; height:100%; background:var(--accent); border-radius:1px; opacity:.75 }} .s .bar i {{ opacity:.45 }}
</style>
<main>
<h1>SerrePositivity 概念の木（{e(VER)}）</h1>
<p>ソースの宣言 <b>{TOT["decls"]:,}</b> 件を、今のファイルとディレクトリを見ずに、主張に現れる定義から概念に分けたもの。大分類 → 概念 → 小概念の三段。小概念は、宣言の多い 26 の概念について中の定義を読んで付けた。行を押すと開く。</p>
<div class="facts"><span><b>{len(G)}</b>大分類</span><span><b>{sum(len(c) for c in G.values())}</b>概念</span><span><b>{sum(1 for r in rows if kind(r["subconcept"])[0] in ("read","aux"))}</b>小概念</span>
<span><b>{st["read"]:,}</b>読んで名前を付けた小概念に入る宣言</span><span><b>{st["aux"]:,}</b>証明の足場（補助）</span><span><b>{st["unread"]:,}</b>まだ読んでいない定義の下</span><span><b>{st["other"] + st["moved"]:,}</b>未分類・移動分</span></div>
<div class="tree"><div class="inner">
<div class="head"><span>概念</span><span>宣言</span><span>（概念の中での割合）</span><span>行</span><span>主定理が使う</span><span>言い換え</span><span>未使用</span></div>
{"".join(H)}
</div></div>
<p>数の読み方：<b>宣言</b>はソースに書いた定理・定義・instance の数（自動生成は親に含める）。<b>主定理が使う</b>は <code>main_statement</code> の証明がたどる宣言の数で、未証明の入力 3 件の向こう側は含まない。<b>言い換え</b>と<b>未使用</b>は機械の判定による割合で、読んで確かめたものではない。<b>補助</b>は、概念というより一つの証明のための足場と判断した定義。文献の節は、定義の docstring にあったもののほか、読んだ担当が推定で添えたものを含む。</p>
</main>'''
open(OUT, 'w', encoding='utf-8').write(page)
print(len(page), dict(st))
