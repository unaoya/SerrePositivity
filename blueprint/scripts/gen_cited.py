"""引用文献の章を Verso Blueprint の章モジュールとして生成する（2026-11-18）。gen_paper.py と同じ作りを文献の表ごとに回す。
正本は research/<key>-coverage/（items.csv の種類・題、review/ch*.csv の状態・宣言・理由、edges.csv の引用の辺、toc.md の見出し）。
scripts/audit2/coverage_blueprint.py から実行する。BS17・BM18・Rydh は目標つきの部 vdescent にまとめる（ROUTES）。
- 各項目は一つのノード。ラベルは <key>_<番号>（式は <key>_eq_…）。文献の中の辺（internal）は (uses := …) に、外の文献への辺は本文に並べる。
- Lean の宣言に結ぶのは状態が none でないもの全部（11-18、ユーザー）。partial・interface は本文の「対応表の状態：」で見分け、serre.js がカードに札を付ける。
- research/<key>-coverage/notes/<番号>.md の原稿があれば項目の本文に、<節>.md は節の頭に入れる（変換は notes_md.py）。"""
import csv, re, sys, os, glob, collections, json
sys.path.insert(0, os.path.dirname(__file__))
from common import Resolver, esc
res = Resolver()
import notes_md
SOURCES = {
 'clmst': ('CLMST', 'CLMST（Cai–Lee–Ma–Schwede–Tucker, Perfectoid signature, perfectoid Hilbert–Kunz multiplicity, …, arXiv 2209.04046v4）'),
 'bs17': ('BS17', 'BS17（Bhatt–Scholze, Projectivity of the Witt vector affine Grassmannian, arXiv 1507.06490v3）'),
 'bm18': ('BM18', 'BM18（Bhatt–Mathew, The arc-topology, arXiv 1807.04725v4）'),
 'rydh': ('Rydh', 'Rydh（Submersions and effective descent of étale morphisms, arXiv 0710.2488v3）'),
 'bs': ('BS', 'BS（Bhatt–Scholze, Prisms and prismatic cohomology、著者版）'),
}
KIND = {'Theorem': 'theorem', 'Lemma': 'lemma_', 'Proposition': 'proposition', 'Corollary': 'corollary', 'Definition': 'definition',
        'Notation': 'definition', 'Construction': 'definition', 'Convention': 'definition', 'Equation': 'definition', 'Example': 'proposition',
        'Remark': 'proposition', 'Claim': 'lemma_', 'Conjecture': 'proposition', 'Question': 'proposition', 'Caution': 'proposition'}
KINDJA = {'Theorem': '定理', 'Lemma': '補題', 'Proposition': '命題', 'Corollary': '系', 'Remark': '注意', 'Equation': '式', 'Definition': '定義',
          'Example': '例', 'Notation': '記法', 'Construction': '構成', 'Convention': '規約', 'Claim': '主張', 'Conjecture': '予想', 'Question': '問い', 'Caution': '注意'}
STATUS = {'own': '本体にある', 'mathlib': 'Mathlib にある', 'both': '本体と Mathlib にある', 'partial': '一部', 'interface': '未証明の入力に依存', 'none': 'なし'}
# 文献をまたぐ辺で、表（edges.csv）にないもの：BS Proposition 8.10（arc 層性）は BS17 Theorem 4.1 (i) を引く（部「v 降下」の目標、11-18）
CROSS = {('bs', '8.10'): ['bs17_4_1']}
def slug(s): return re.sub(r'[^0-9A-Za-z]+', '_', s).strip('_')
def skey(s): return [(0, int(x)) if x.isdigit() else (1, x) for x in re.split(r'[.]', s) if x != '']
def gen(key):
    dirname, title = SOURCES[key]
    P = f'research/{key}-coverage'; OUT = f'blueprint/SerreBlueprint/{dirname}'
    os.makedirs(OUT, exist_ok=True)
    for old in glob.glob(f'{OUT}/Section*.lean'): os.remove(old)
    items = list(csv.DictReader(open(f'{P}/items.csv', encoding='utf-8')))
    rev = {}
    for f in sorted(glob.glob(f'{P}/review/ch*.csv')):
        for r in csv.DictReader(open(f, encoding='utf-8')): rev[r['number']] = r
    edges = list(csv.DictReader(open(f'{P}/edges.csv', encoding='utf-8'))) if os.path.exists(f'{P}/edges.csv') else []
    heads = {}
    if os.path.exists(f'{P}/toc.md'):
        for l in open(f'{P}/toc.md', encoding='utf-8'):
            m = re.match(r'\|\s*([0-9A-Z]+(?:\.[0-9]+)*)\s*\|\s*([^|]+?)\s*\|', l)
            if m: heads.setdefault(m.group(1), m.group(2))
    def label(n):
        if n.startswith('('): return f'{key}_eq_' + slug(n.strip('()'))
        return f'{key}_' + slug(n)
    def section(r):
        s = r.get('section') or ''
        if s: return s
        n = r['number'].strip('()'); return n.split('.')[0]
    known = {r['number'] for r in items}
    uses = collections.defaultdict(list); ext = collections.defaultdict(list)
    for e in edges:
        if e['kind'] == 'internal' and e['depends_on'] in known and e['depends_on'] != e['number']:
            if label(e['depends_on']) not in uses[e['number']]: uses[e['number']].append(label(e['depends_on']))
        elif e['kind'] == 'external' and e['depends_on'] not in ext[e['number']]: ext[e['number']].append(e['depends_on'])
    by_sec = collections.defaultdict(list)
    for r in items: by_sec[section(r).split('.')[0]].append(r)
    stats = collections.Counter(); modules = []; seen_labels = set()
    STMT = notes_md.statements(P)   # 主張の一行（NB-W4）
    for sec in sorted(by_sec, key=skey):
        imports = set(); body = []
        subs = collections.defaultdict(list)
        for r in by_sec[sec]: subs[section(r)].append(r)
        for sub in sorted(subs, key=skey):
            if sub != sec:
                body.append(f'# §{sub} {esc(heads.get(sub, ""))}\n')
                body.append('%%%\nnumber := false\ntag := "' + f'{key}-' + slug(sub).replace('_', '-') + '"\n%%%\n')
                if (nb := notes_md.note_body(f'{P}/notes/{sub}.md', skip=('原典 ', '照合先'))): body.append(nb)
            for r in subs[sub]:
                n = r['number']; rv = rev.get(n, {}); st = rv.get('status', '') or 'none'
                lab = label(n)
                if lab in seen_labels: continue
                seen_labels.add(lab)
                linked = res.links(lab, rv.get('declarations', ''), imports, st in ('own', 'mathlib', 'both', 'partial', 'interface'))
                stats[st] += 1; stats['linked' if linked else 'nolink'] += 1
                opts = ''
                if linked: opts += f' (lean := "{", ".join(linked)}")'
                us = uses[n] + [x for x in CROSS.get((key, n), []) if x not in uses[n]]
                if us: opts += f' (uses := "{", ".join(us)}")'
                ttl = r.get('title_ja') or r.get('title') or ''
                ttl = re.sub(r'<[^>]+>', '', ttl)
                pk = rv.get('partial_kind', '')
                state = STATUS.get(st, st) + (f'（{pk}）' if st == 'partial' and pk else '')
                body.append(f':::{KIND.get(r["kind"], "proposition")} "{lab}"{opts}')
                body.append(f'*{KINDJA.get(r["kind"], esc(r["kind"]))} {esc(n)}*　{esc(ttl)}。対応表の状態：{state}。\n')
                if n in STMT: body.append(STMT[n]); stats['with-statement'] += 1
                if rv.get('reason'): body.append(esc(rv['reason']) + '\n')
                if (nb := notes_md.note_body(f'{P}/notes/{n}.md', skip=('原典 ', '照合先'))):
                    stats['with-note'] += 1; body.append(nb)
                if declaration_note := res.declaration_note(lab, rv.get('declarations', ''), linked): body.append(declaration_note)
                if ext[n]: body.append('外の文献：' + '、'.join(esc(x) for x in ext[n]) + '\n')
                body.append(':::\n')
        mod = f'Section{slug(sec)}'
        head = esc(heads.get(sec, ''))
        hdr = ['import Verso', 'import VersoManual', 'import VersoBlueprint'] + [f'import {m}' for m in sorted(imports)] + \
              ['', 'open Verso.Genre', 'open Verso.Genre.Manual', 'open Informal', '', '-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）', 'set_option maxHeartbeats 2000000', '',
               f'#doc (Manual) "§{sec} {re.sub(r"[][]", "", heads.get(sec, ""))}" =>', '%%%', 'number := false', f'tag := "{key}-{slug(sec)}"', '%%%', '',
               f'{dirname} §{sec} の項目と、本体の宣言との対応。本文は対応表（`research/{key}-coverage`）の照合の理由で、原典の本文の写しではない。\n']
        if (nb := notes_md.note_body(f'{P}/notes/{sec}.md', skip=('原典 ', '照合先'))): hdr.append(nb)
        res.write(f'{OUT}/{mod}.lean', '\n'.join(hdr + body) + '\n')
        modules.append(mod)
    json.dump({'key': key, 'dir': dirname, 'title': title, 'modules': modules, 'stats': dict(stats)},
              open(f'{OUT}/generated.json', 'w'), ensure_ascii=False, indent=1)
    print(key, len(modules), 'sections', dict(stats))
# 目標つきの部（11-18、ユーザー）：BS17・BM18・Rydh は文献ごとの部にせず、BS が引用する BS17 Theorem 4.1 (i) を目標にした一つの部にして、
# 必要な項目だけを載せる。「必要」は、対応表で本体か Mathlib に対応がある項目（状態が none でないもの）＝形式化の経路が実際に使ったもの、と目標。
# 文献の中の辺に加えて、文献をまたぐ辺（edges.csv の external で「Rydh 2.2」の形のもの）も、載せた項目どうしなら (uses := …) にする。
ROUTES = {
 'vdescent': dict(dir='VDescent', title='v 降下（目標：BS17 Theorem 4.1 (i) と BM18 Proposition 4.8。BS17・BM18・Rydh の必要な項目）', goals=[('bs17', '4.1'), ('bm18', '4.8')],
                  route_edges='research/bs17-coverage/route-edges.csv',
                  sources=['bs17', 'bm18', 'rydh'],
                  intro='目標は二つ。BS17 Theorem 4.1 (i)（完全スキームの上の v 降下、BS Proposition 8.10 が引用する）と、BM18 Proposition 4.8（aic-v 切除を満たす finitary v 層は arc 層）。本体は BS17 4.1 (i) のうち n = 1・E = O・アフィン・有限族の場合を作り、BM18 4.8 は構造層の場合を、その BS17 4.1 を入力にして作った（どちらも対応表では「一部」）。この部には、三つの文献の項目のうち、本体か Mathlib に対応があるものだけを載せる。辺は本体の経路（宣言どうしの参照、`research/bs17-coverage/route-edges.csv`）で、原典の引用の辺ではない。二つの目標から辺をたどって届かない項目は、本体に対応はあるが経路には使っていないもの。全項目の表は `research/bs17-coverage`・`bm18-coverage`・`rydh-coverage`。'),
}
def gen_route(rk):
    R = ROUTES[rk]; OUT = f'blueprint/SerreBlueprint/{R["dir"]}'
    os.makedirs(OUT, exist_ok=True)
    for old in glob.glob(f'{OUT}/*.lean'): os.remove(old)
    data = {}; included = {}
    def label(key, n):
        return f'{key}_eq_' + slug(n.strip('()')) if n.startswith('(') else f'{key}_' + slug(n)
    for key in R['sources']:
        P = f'research/{key}-coverage'
        items = list(csv.DictReader(open(f'{P}/items.csv', encoding='utf-8')))
        rev = {}
        for f in sorted(glob.glob(f'{P}/review/ch*.csv')):
            for r in csv.DictReader(open(f, encoding='utf-8')): rev[r['number']] = r
        edges = list(csv.DictReader(open(f'{P}/edges.csv', encoding='utf-8')))
        heads = {}
        for l in open(f'{P}/toc.md', encoding='utf-8'):
            m = re.match(r'\|\s*([0-9A-Z]+(?:\.[0-9]+)*)\s*\|\s*([^|]+?)\s*\|', l)
            if m: heads.setdefault(m.group(1), m.group(2))
        keep = [r for r in items if (rev.get(r['number'], {}).get('status') or 'none') != 'none' or (key, r['number']) in R['goals']]
        data[key] = (keep, rev, edges, heads, notes_md.statements(P)); included[key] = {r['number'] for r in keep}
    abbr = {SOURCES[k][0]: k for k in R['sources']}
    route = list(csv.DictReader(open(R['route_edges'], encoding='utf-8')))
    modules = []; stats = collections.Counter()
    for key in R['sources']:
        keep, rev, edges, heads, STMT = data[key]; dirname = SOURCES[key][0]
        uses = collections.defaultdict(list); ext = collections.defaultdict(list)
        # 辺は本体の経路（route-edges.csv、NB-W4）。原典の引用の辺（edges.csv）は、外の文献の一覧にだけ使う
        for e in route:
            if e['source'] == key and e['number'] in included[key] and e['depends_on_number'] in included.get(e['depends_on_source'], ()):
                tgt = label(e['depends_on_source'], e['depends_on_number'])
                if tgt != label(key, e['number']) and tgt not in uses[e['number']]: uses[e['number']].append(tgt)
        for e in edges:
            n, d = e['number'], e['depends_on']
            if n not in included[key]: continue
            tgt = None
            if e['kind'] == 'internal': continue
            else:
                m = re.match(r'(\S+) (\S+)$', d)
                if m and m.group(1) in abbr and m.group(2) in included[abbr[m.group(1)]]: continue
                elif d not in ext[n]: ext[n].append(d)
        imports = set(); body = []; cur = None; seen = set()
        for r in sorted(keep, key=lambda r: skey((r.get('section') or r['number'].strip('()')).split('.')[0])):
            n = r['number']; rv = rev.get(n, {}); st = rv.get('status', '') or 'none'; lab = label(key, n)
            if lab in seen: continue
            seen.add(lab)
            sec = (r.get('section') or n.strip('()')).split('.')[0]
            if sec != cur:
                cur = sec
                body.append(f'# §{sec} {esc(heads.get(sec, ""))}\n')
                body.append('%%%\nnumber := false\ntag := "' + f'{rk}-{key}-{slug(sec)}' + '"\n%%%\n')
            linked = res.links(lab, rv.get('declarations', ''), imports, st in ('own', 'mathlib', 'both', 'partial', 'interface'))
            stats[st] += 1
            opts = ''
            if linked: opts += f' (lean := "{", ".join(linked)}")'
            if uses[n]: opts += f' (uses := "{", ".join(uses[n])}")'
            ttl = re.sub(r'<[^>]+>', '', r.get('title_ja') or r.get('title') or '')
            pk = rv.get('partial_kind', '')
            state = STATUS.get(st, st) + (f'（{pk}）' if st == 'partial' and pk else '')
            goal = '【この部の目標】' if (key, n) in R['goals'] else ''
            body.append(f':::{KIND.get(r["kind"], "proposition")} "{lab}"{opts}')
            body.append(f'*{dirname} {KINDJA.get(r["kind"], esc(r["kind"]))} {esc(n)}*　{goal}{esc(ttl)}。対応表の状態：{state}。\n')
            if n in STMT: body.append(STMT[n]); stats['with-statement'] += 1
            if rv.get('reason'): body.append(esc(rv['reason']) + '\n')
            if declaration_note := res.declaration_note(lab, rv.get('declarations', ''), linked): body.append(declaration_note)
            if ext[n]: body.append('外の文献：' + '、'.join(esc(x) for x in ext[n]) + '\n')
            body.append(':::\n')
        hdr = ['import Verso', 'import VersoManual', 'import VersoBlueprint'] + [f'import {m}' for m in sorted(imports)] + \
              ['', 'open Verso.Genre', 'open Verso.Genre.Manual', 'open Informal', '', '-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）', 'set_option maxHeartbeats 2000000', '',
               f'#doc (Manual) "{SOURCES[key][1]}" =>', '%%%', 'number := false', f'tag := "{rk}-{key}"', '%%%', '',
               (R['intro'] + '\n') if key == R['sources'][0] else f'{dirname} の項目のうち、この経路で本体か Mathlib に対応があるもの。\n']
        res.write(f'{OUT}/{dirname}.lean', '\n'.join(hdr + body) + '\n')
        modules.append(dirname)
    json.dump({'key': rk, 'dir': R['dir'], 'title': R['title'], 'modules': modules, 'stats': dict(stats)},
              open(f'{OUT}/generated.json', 'w'), ensure_ascii=False, indent=1)
    print(rk, modules, dict(stats))
for k in sys.argv[1:]: (gen_route if k in ROUTES else gen)(k)
