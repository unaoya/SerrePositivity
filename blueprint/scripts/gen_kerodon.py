"""Kerodon の章を Verso Blueprint の章モジュールとして生成する（2026-11-16、試作）。
正本は research/kerodon-coverage/（review/ch<N>.csv の状態・宣言・判定の理由、item-tags.csv の Tag、toc.md の見出し）。
この生成物を手で直さない。表を直して生成し直す。
使い方（リポジトリの root で）：python3 blueprint/scripts/gen_kerodon.py 1
- 各項目は一つのノード。ラベルは kerodon_<番号>（点を _ に）。
- 状態が own・mathlib・both で、宣言が今のソースで一意に解決できるものだけ (lean := …) で結ぶ。partial は本文に宣言名を挙げるだけ（結ぶと形式化済みに数えられるため）。
- 本文は対応表の判定の理由（日本語の要約）。Kerodon の本文は写さず、Tag へリンクする。"""
import csv, re, os, sys, glob, collections, json
ch = sys.argv[1]
K = 'research/kerodon-coverage'
OUT = 'blueprint/SerreBlueprint/Kerodon'
# 見出し
def plain_title(s):
    """見出しの TeX を平文に（Verso の題は文字列なので、TeX の \\ は書けない）。"""
    def tex(m):
        x = m.group(1)
        x = x.replace('\\infty', '∞').replace('\\rightarrow', '→').replace('\\bullet', '•').replace('\\pi', 'π')
        x = re.sub(r'\\(?:operatorname|mathcal|mathrm|mathbf|mathbb)\s*', '', x)
        x = re.sub(r'\\[A-Za-z]+', '', x)
        return re.sub(r'\s+', ' ', x.replace('{', '').replace('}', '').replace('_ ', '_')).strip()
    return re.sub(r'\$([^$]*)\$', tex, s)
toc = {}
for l in open(f'{K}/toc.md', encoding='utf-8'):
    m = re.match(r'\s*- (?:Chapter )?([0-9]+(?:\.[0-9]+)*) \[([0-9A-Z]{4})\] (.*)$', l)
    if m: toc[m.group(1)] = (m.group(2), plain_title(m.group(3)))
tags = {r['number']: r['tag'] for r in csv.DictReader(open(f'{K}/item-tags.csv', encoding='utf-8'))}
kinds = {r['number']: r['kind'] for r in csv.DictReader(open(f'{K}/items.csv', encoding='utf-8'))}
rows = list(csv.DictReader(open(f'{K}/review/ch{ch}.csv', encoding='utf-8')))
# review に行のない項目（照合の対象外にした Remark・Example など）のうち、原稿（notes/<番号>.md）があるものは節点を作って本文を出す（11-18）
_have = {r['number'] for r in rows}
for _n in sorted(kinds):
    if _n.split('.')[0] == str(ch) and _n not in _have and os.path.exists(f'{K}/notes/{_n}.md'):
        rows.append({'number': _n, 'status_new': 'unreviewed', 'declarations_new': '', 'reason': ''})
# 宣言の完全な名前（名前空間つきの走査、refresh_by_source.py と同じ規則）
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|public|scoped|local|partial|unsafe)\s+)*(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)\s+([^\s:({\[]+)')
NS = re.compile(r'^\s*namespace\s+(\S+)'); SEC = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|public\s+)*section(?:\s+(\S+))?\s*$'); END = re.compile(r'^\s*end(?:\s+(\S+))?\s*$')
index = collections.defaultdict(list)
def scan(path, rel, mod):
    stack = []
    for i, l in enumerate(open(path, encoding='utf-8', errors='ignore'), 1):
        if (m := NS.match(l)): stack.append(m.group(1).split('.')); continue
        if SEC.match(l): stack.append([]); continue
        if END.match(l) and stack: stack.pop(); continue
        if (m := DECL.match(l)):
            n = m.group(2)
            full = n[7:] if n.startswith('_root_.') else '.'.join([p for ps in stack for p in ps] + [n])
            index[full].append(mod)
paths = set()
for r in rows:
    for e in r['declarations_new'].split(' | '):
        if ' @ ' in e: paths.add(e.split(' @ ', 1)[1].rsplit(':', 1)[0])
for p in paths:
    fp = p if p.startswith('SerrePositivity/') else '.lake/packages/mathlib/' + p
    if os.path.exists(fp): scan(fp, p, p[:-5].replace('/', '.'))
by_suffix = collections.defaultdict(set)
for full in index:
    parts = full.split('.')
    for k in range(len(parts)): by_suffix['.'.join(parts[k:])].add(full)
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_.'₀-₉!?]*$")
def resolve(entry):
    if ' @ ' not in entry: return None
    name = entry.split(' @ ', 1)[0].split('（')[0].split(' (')[0].strip()
    if not IDENT.match(name): return None
    c = by_suffix.get(name, set())
    if len(c) != 1: return None
    full = next(iter(c)); return full, index[full][0]
KIND = {'Definition': 'definition', 'Notation': 'definition', 'Construction': 'definition', 'Variant': 'definition',
        'Theorem': 'theorem', 'Proposition': 'proposition', 'Lemma': 'lemma_', 'Corollary': 'corollary'}
def esc(s):
    return re.sub(r'([\\*_`\[\]{}#$<>|~^])', r'\\\1', s)

# NB-W1（11-17）：research/kerodon-coverage/notes/<番号>.md の原稿をノードの本文に入れる（変換は notes_md.py）。
import notes_md
NOTES = f'{K}/notes'
def note_body(n): return notes_md.note_body(f'{NOTES}/{n}.md', skip=('Kerodon [', '照合先'))

# 依存の辺：P⁰ の項目の閉包（research/p0-lurie/item-closure/edges.csv）のうち Kerodon → Kerodon の辺を (uses := …) に
ALLNUM = set()
for f in glob.glob(f'{K}/review/ch*.csv'):
    for r in csv.DictReader(open(f, encoding='utf-8')): ALLNUM.add(r['number'])
USES = collections.defaultdict(list)
_e = 'research/p0-lurie/item-closure/edges.csv'
if os.path.exists(_e):
    for e in csv.DictReader(open(_e, encoding='utf-8')):
        if e['source'] == 'Kerodon' and e['depends_on_source'] == 'Kerodon' and e['number'] in ALLNUM and e['depends_on_number'] in ALLNUM:
            if e['depends_on_number'] not in USES[e['number']]: USES[e['number']].append(e['depends_on_number'])

STATUS = {'unreviewed': '照合の対象外', 'own': '本体にある', 'mathlib': 'Mathlib にある', 'both': '本体と Mathlib にある', 'partial': '一部', 'none': 'なし'}
by_sec = collections.defaultdict(list)
for r in rows:
    n = r['number']; by_sec['.'.join(n.split('.')[:2])].append(r)
stats = collections.Counter(); modules = []
for sec in sorted(by_sec, key=lambda s: [int(x) for x in s.split('.')]):
    imports = set(); body = []
    sub_rows = collections.defaultdict(list)
    for r in by_sec[sec]: sub_rows['.'.join(r['number'].split('.')[:3])].append(r)
    for sub in sorted(sub_rows, key=lambda s: [int(x) for x in s.split('.')]):
        t = toc.get(sub)
        if not sub.endswith('.0'):
            # 番号は Kerodon の番号を見出しに書き、Verso の自動番号は切る。HTML の id は tag で ASCII に
            body.append(f'# {sub} {esc(t[1]) if t else ""}\n')
            body.append('%%%\nnumber := false\ntag := "kerodon-' + sub.replace('.', '-') + '"\n%%%\n')
            if t: body.append(f'Kerodon [Tag {t[0]}](https://kerodon.net/tag/{t[0]})\n')
            if (nb := note_body(sub)):
                stats['with-note-intro'] += 1
                body.append(nb)
        # x.y.0 の項目（節の冒頭）は見出しを立てずに節の本文の先頭に置く
        for r in sorted(sub_rows[sub], key=lambda r: [int(x) for x in r['number'].split('.')]):
            n = r['number']; kind = kinds.get(n, 'Proposition'); st = r['status_new']
            directive = KIND.get(kind, 'proposition')
            label = 'kerodon_' + n.replace('.', '_')
            decls = [e.strip() for e in r['declarations_new'].split(' | ') if e.strip()]
            linked = []
            if st in ('own', 'mathlib', 'both', 'partial', 'interface'):
                for e in decls:
                    x = resolve(e)
                    if x: linked.append(x[0]); imports.add(x[1])
            stats['linked' if linked else ('nolink-' + st)] += 1
            opt = f' (lean := "{", ".join(linked)}")' if linked else ''
            us = [u for u in USES.get(n, []) if u != n]
            if us: opt += ' (uses := "' + ', '.join('kerodon_' + u.replace('.', '_') for u in us) + '")'; stats['with-uses'] += 1
            tag = tags.get(n)
            head = f'Kerodon {kind} {n}' + (f'（[Tag {tag}](https://kerodon.net/tag/{tag})）' if tag else '')  # 自前の markup なので esc しない
            body.append(f':::{directive} "{label}"{opt}')
            body.append(f'{head}。対応表の状態：{STATUS.get(st, st)}。\n')
            if r['reason']: body.append(esc(r['reason']) + '\n')
            if (nb := note_body(n)):
                stats['with-note'] += 1
                body.append(nb)
            if decls and not linked:
                body.append('宣言：' + '、'.join('`' + e.split(' @ ', 1)[0].replace('`', '') + '`' for e in decls) + '\n')
            body.append(':::\n')
    t = toc.get(sec)
    mod = 'Section' + sec.replace('.', '_')
    hdr = ['import Verso', 'import VersoManual', 'import VersoBlueprint'] + [f'import {m}' for m in sorted(imports)] + \
          ['', 'open Verso.Genre', 'open Verso.Genre.Manual', 'open Informal', '', '-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）', 'set_option maxHeartbeats 2000000', '',
           f'#doc (Manual) "{sec} {t[1] if t else ""}" =>', '%%%', 'number := false', f'tag := "kerodon-{sec.replace(".", "-")}"', '%%%', '',
           f'Kerodon の {sec} 節（[Tag {t[0]}](https://kerodon.net/tag/{t[0]})）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。\n' if t else '']
    if (nb := note_body(sec)):
        stats['with-note-intro'] += 1
        hdr.append(nb)
    open(f'{OUT}/{mod}.lean', 'w', encoding='utf-8').write('\n'.join(hdr + body) + '\n')
    modules.append(mod)
json.dump({'chapter': ch, 'modules': modules, 'stats': dict(stats)}, open(f'{OUT}/ch{ch}-generated.json', 'w'), ensure_ascii=False, indent=1)
print(modules, dict(stats))
