"""本論文の章を Verso Blueprint の章モジュールとして生成する（2026-11-17、試作）。
正本は research/paper-coverage/（items.csv の種類・見出し、review/ch<N>.csv の状態・宣言・理由、edges.csv の引用の辺、toc.md の見出し）。
生成物を手で直さない。表を直して生成し直す。使い方（リポジトリの root で）：python3 blueprint/scripts/gen_paper.py
- 各項目は一つのノード。ラベルは paper_<番号>（式は paper_eq_…、図は paper_fig_…）。
- 論文の中の辺（edges.csv の internal）は (uses := …) に。外の文献への辺（external）は本文に文献と番号を並べる。
- Lean の宣言に結ぶのは状態が own のものだけ（interface・partial は本文に宣言名と状態を書く。結ぶと形式化済みに数えられるため）。
- 外の文献の辺（external）は、引用先ごとのノードに (uses := …) で張る（11-17、CC-W2）：CLMST は CLMST の部のノード clmst_…、それ以外は research/paper-coverage/external.csv から作る「引用した結果」のノード ext_…（Paper/External.lean）。"""
import csv, re, sys, os, collections, json
sys.path.insert(0, os.path.dirname(__file__))
from common import Resolver, paths_of, esc
P = 'research/paper-coverage'; OUT = 'blueprint/SerreBlueprint/Paper'
items = list(csv.DictReader(open(f'{P}/items.csv', encoding='utf-8')))
rev = {}
for ch in range(1, 6):
    for r in csv.DictReader(open(f'{P}/review/ch{ch}.csv', encoding='utf-8')): rev[r['number']] = r
edges = list(csv.DictReader(open(f'{P}/edges.csv', encoding='utf-8')))
heads = {}
for l in open(f'{P}/toc.md', encoding='utf-8'):
    m = re.match(r'\|\s*([0-9]+(?:\.[0-9]+)?)\s*\|\s*([^|]+?)\s*\|\s*([0-9]+)\s*\|', l)
    if m: heads.setdefault(m.group(1), m.group(2))
def label(n):
    if n.startswith('('): return 'paper_eq_' + n.strip('()').replace('.', '_')
    if n.startswith('Figure'): return 'paper_fig_' + n.split()[-1]
    return 'paper_' + n.replace('.', '_')
known = {r['number'] for r in items}
uses = collections.defaultdict(list); ext = collections.defaultdict(list)
for e in edges:
    if e['kind'] == 'internal' and e['depends_on'] in known and e['depends_on'] != e['number']:
        if label(e['depends_on']) not in uses[e['number']]: uses[e['number']].append(label(e['depends_on']))
    elif e['kind'] == 'external':
        if e['depends_on'] not in ext[e['number']]: ext[e['number']].append(e['depends_on'])
external = list(csv.DictReader(open(f'{P}/external.csv', encoding='utf-8')))
def slug(s): return re.sub(r'[^0-9A-Za-z]+', '_', s).strip('_')
def ext_label(src_num):
    parts = src_num.split(' ', 1); source = parts[0]; num = parts[1] if len(parts) > 1 else ''
    if source == 'CLMST' and num: return 'clmst_' + slug(num.split('(')[0])  # 2.2.6(a) は項目 2.2.6 のノード
    return 'ext_' + source + ('_' + slug(num) if num else '')
res = Resolver(paths_of(r['declarations'] for r in list(rev.values()) + external))
KIND = {'Theorem': 'theorem', 'Lemma': 'lemma_', 'Proposition': 'proposition', 'Corollary': 'corollary', 'Remark': 'proposition', 'Equation': 'definition', 'Figure': 'definition', 'Definition': 'definition'}
KINDJA = {'Theorem': '定理', 'Lemma': '補題', 'Proposition': '命題', 'Corollary': '系', 'Remark': '注意', 'Equation': '式', 'Figure': '図', 'Definition': '定義'}
STATUS = {'own': '本体にある', 'mathlib': 'Mathlib にある', 'both': '本体と Mathlib にある', 'partial': '一部', 'interface': '未証明の入力に依存', 'none': 'なし'}
by_sec = collections.defaultdict(list)
for r in items: by_sec[r['section'].split('.')[0]].append(r)
stats = collections.Counter(); modules = []
for sec in sorted(by_sec, key=int):
    imports = set(); body = []
    subs = collections.defaultdict(list)
    for r in by_sec[sec]: subs[r['section']].append(r)
    for sub in sorted(subs, key=lambda s: [int(x) for x in s.split('.')]):
        if sub != sec:
            body.append(f'# §{sub} {esc(heads.get(sub, ""))}\n')
            body.append('%%%\nnumber := false\ntag := "paper-' + sub.replace('.', '-') + '"\n%%%\n')
        for r in subs[sub]:
            n = r['number']; rv = rev.get(n, {}); st = rv.get('status', '')
            linked = []
            if st == 'own':
                for e in [x.strip() for x in rv.get('declarations', '').split(' | ') if x.strip()]:
                    x = res.resolve(e)
                    if x: linked.append(x[0]); imports.add(x[1])
            stats['linked' if linked else 'nolink-' + (st or '?')] += 1
            opts = ''
            if linked: opts += f' (lean := "{", ".join(linked)}")'
            all_uses = uses[n] + [ext_label(x) for x in ext[n] if ext_label(x) not in uses[n]]
            if all_uses: opts += f' (uses := "{", ".join(all_uses)}")'
            title = r['title']
            body.append(f':::{KIND.get(r["kind"], "proposition")} "{label(n)}"{opts}')
            body.append(f'**{KINDJA.get(r["kind"], r["kind"])} {esc(n)}**　{esc(title)}。対応表の状態：{STATUS.get(st, st)}。\n')
            if rv.get('reason'): body.append(esc(rv['reason']) + '\n')
            decls = [x.split(' @ ', 1)[0].strip() for x in rv.get('declarations', '').split(' | ') if x.strip()]
            if decls and not linked:
                body.append('宣言：' + '、'.join('`' + d.replace('`', '') + '`' for d in decls) + '\n')
            if ext[n]:
                body.append('外の文献：' + '、'.join(esc(x) for x in ext[n]) + '\n')
            body.append(':::\n')
    mod = f'Section{sec}'
    hdr = ['import Verso', 'import VersoManual', 'import VersoBlueprint'] + [f'import {m}' for m in sorted(imports)] + \
          ['', 'open Verso.Genre', 'open Verso.Genre.Manual', 'open Informal', '',
           f'#doc (Manual) "§{sec} {heads.get(sec, "")}" =>', '%%%', 'number := false', f'tag := "paper-{sec}"', '%%%', '',
           f'本論文 §{sec} の項目と、本体の宣言との対応。本文は対応表（`research/paper-coverage`）の照合の理由で、論文の本文の写しではない。\n']
    open(f'{OUT}/{mod}.lean', 'w', encoding='utf-8').write('\n'.join(hdr + body) + '\n')
    modules.append(mod)
# 引用した結果（external.csv）：CLMST は CLMST の部にノードがあるので除く
imports = set(); body = []
for r in external:
    if r['source'] == 'CLMST': continue
    lab = ext_label((r['source'] + ' ' + r['number']).strip()); st = r['status']
    linked = []
    if st in ('own', 'mathlib', 'both'):
        for e in [x.strip() for x in r['declarations'].split(' | ') if x.strip()]:
            x = res.resolve(e)
            if x: linked.append(x[0]); imports.add(x[1])
    stats['ext-linked' if linked else 'ext-nolink-' + (st or 'table')] += 1
    opts = f' (lean := "{", ".join(linked)}")' if linked else ''
    body.append(f':::proposition "{lab}"{opts}')
    body.append(f'*{esc((r["source"] + " " + r["number"]).strip())}*　{esc(r["statement_ja"])}。' + (f'対応表の状態：{STATUS.get(st, st)}。' if st else '状態はその文献の対応表を参照。') + '\n')
    if r.get('reason'): body.append(esc(r['reason']) + '\n')
    decls = [x.split(' @ ', 1)[0].strip() for x in r['declarations'].split(' | ') if x.strip()]
    if decls and not linked: body.append('宣言：' + '、'.join('`' + d.replace('`', '') + '`' for d in decls) + '\n')
    body.append(':::\n')
hdr = ['import Verso', 'import VersoManual', 'import VersoBlueprint'] + [f'import {m}' for m in sorted(imports)] + \
      ['', 'open Verso.Genre', 'open Verso.Genre.Manual', 'open Informal', '',
       '#doc (Manual) "引用した結果" =>', '%%%', 'number := false', 'tag := "paper-external"', '%%%', '',
       '本論文が引用する外の文献の結果（`research/paper-coverage/external.csv`）。各本論文の項目から uses で張られる。CLMST の結果は CLMST の部のノード。BS19・K の文献の結果は、それぞれの対応表ができるまで状態を空にしてある。\n']
open(f'{OUT}/External.lean', 'w', encoding='utf-8').write('\n'.join(hdr + body) + '\n')
modules.append('External')
json.dump({'modules': modules, 'stats': dict(stats)}, open(f'{OUT}/paper-generated.json', 'w'), ensure_ascii=False, indent=1)
print(modules, dict(stats))
