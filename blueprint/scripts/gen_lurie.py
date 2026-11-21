"""HTT・HA の部を Verso Blueprint の章モジュールとして生成する（2026-11-19、NB-W5）。
正本は research/<key>-coverage/（items.csv の種類・題・節、review/ch*.csv の状態・宣言・理由、statements.csv の主張、notes/ の原稿、toc.md の見出し）。
scripts/audit2/coverage_blueprint.py から実行する。
- 載せるのは対応表の状態が none でない項目だけ（本体か Mathlib に対応があるもの、原稿もこの範囲で書いた）。全項目の表は research/<key>-coverage。
- 一つの節（x.y）を一つのモジュールに、小節（x.y.z）を見出しに。ラベルは <key>_<番号>（点を _ に）。
- 辺は P⁰ の項目の閉包（research/p0-lurie/item-closure/edges.csv）のうち、HTT・HA・Kerodon の載せた項目どうしのもの。
- Lean の宣言に結ぶのは状態が none でないもの全部（gen_cited.py と同じ）。"""
import csv, re, sys, os, glob, collections, json
sys.path.insert(0, os.path.dirname(__file__))
from common import Resolver, esc
res = Resolver()
import notes_md
KIND = {'Theorem': 'theorem', 'Lemma': 'lemma_', 'Proposition': 'proposition', 'Corollary': 'corollary', 'Definition': 'definition',
        'Notation': 'definition', 'Construction': 'definition', 'Convention': 'definition', 'Equation': 'definition', 'Example': 'proposition',
        'Remark': 'proposition', 'Claim': 'lemma_', 'Conjecture': 'proposition', 'Question': 'proposition', 'Caution': 'proposition'}
KINDJA = {'Theorem': '定理', 'Lemma': '補題', 'Proposition': '命題', 'Corollary': '系', 'Remark': '注意', 'Equation': '式', 'Definition': '定義',
          'Example': '例', 'Notation': '記法', 'Construction': '構成', 'Convention': '規約', 'Claim': '主張', 'Conjecture': '予想', 'Question': '問い', 'Caution': '注意'}
STATUS = {'own': '本体にある', 'mathlib': 'Mathlib にある', 'both': '本体と Mathlib にある', 'partial': '一部', 'interface': '未証明の入力に依存', 'none': 'なし'}
KIND = dict(KIND, Fact='proposition', Variant='definition', Warning='proposition', Counterexample='proposition')
KINDJA = dict(KINDJA, Fact='事実', Variant='変種', Warning='警告', Counterexample='反例')
SOURCES = {
 'htt': ('HTT', 'HTT', 'HTT（Lurie, Higher Topos Theory、著者公開版 2017-04-09）'),
 'ha': ('HA', 'HA', 'HA（Lurie, Higher Algebra、著者公開版 2017-09-18）'),
}
def slug(s): return re.sub(r'[^0-9A-Za-z]+', '_', s).strip('_')
def skey(s): return [(0, int(x)) if x.isdigit() else (1, x) for x in s.split('.') if x]
def plain(s):
    """見出しの TeX を平文に（Verso の題は文字列）。"""
    def tex(m):
        x = m.group(1).replace('\\Delta', 'Δ').replace('\\infty', '∞').replace('\\mathfrak P', '𝔓').replace('\\mathfrak{P}', '𝔓')
        x = re.sub(r'\\(?:operatorname|mathcal|mathrm|mathbf|mathbb|mathfrak)\s*', '', x)
        x = re.sub(r'\\[A-Za-z]+', '', x)
        return re.sub(r'\s+', ' ', x.replace('{', '').replace('}', '')).strip()
    return re.sub(r'\$([^$]*)\$', tex, s)
def label(key, n): return f'{key}_' + slug(n)
def load(key):
    P = f'research/{key}-coverage'
    items = list(csv.DictReader(open(f'{P}/items.csv', encoding='utf-8')))
    rev = {}
    for f in sorted(glob.glob(f'{P}/review/ch*.csv')):
        for r in csv.DictReader(open(f, encoding='utf-8')): rev[r['number']] = r
    keep = [r for r in items if (rev.get(r['number'], {}).get('status') or 'none') != 'none']
    heads = {}
    for l in open(f'{P}/toc.md', encoding='utf-8'):
        m = re.match(r'\s*(?:- |### 第 )([0-9AB]+(?:\.[0-9]+)*)(?: 章)? (.*?)\s*(?:（p\.|\(p\.|$)', l)
        if m: heads.setdefault(m.group(1), plain(m.group(2).strip()))
    return P, keep, rev, heads
DATA = {k: load(k) for k in SOURCES}
INCL = {SOURCES[k][1]: {r['number'] for r in DATA[k][1]} for k in SOURCES}
LAB = {'HTT': 'htt', 'HA': 'ha'}
INCL['Kerodon'] = set()
for f in glob.glob('research/kerodon-coverage/review/ch*.csv'):
    for r in csv.DictReader(open(f, encoding='utf-8')): INCL['Kerodon'].add(r['number'])
LAB['Kerodon'] = 'kerodon'
USES = collections.defaultdict(list)
_e = 'research/p0-lurie/item-closure/edges.csv'
if os.path.exists(_e):
    for e in csv.DictReader(open(_e, encoding='utf-8')):
        s, t = e['source'], e['depends_on_source']
        if s in ('HTT', 'HA') and t in INCL and e['number'] in INCL[s] and e['depends_on_number'] in INCL[t]:
            tgt = label(LAB[t], e['depends_on_number'])
            if tgt != label(LAB[s], e['number']) and tgt not in USES[(s, e['number'])]: USES[(s, e['number'])].append(tgt)
def gen(key):
    dirname, abbr, title = SOURCES[key]
    P, keep, rev, heads = DATA[key]; OUT = f'blueprint/SerreBlueprint/{dirname}'
    os.makedirs(OUT, exist_ok=True)
    for old in glob.glob(f'{OUT}/*.lean'): os.remove(old)
    STMT = notes_md.statements(P)
    def pdf(n):
        fp = f'{P}/notes/{n}.md'
        if not os.path.exists(fp): return ''
        m = re.search(r'^\[[^\]]*原典 PDF\]\((https?://[^)]+)\)', open(fp, encoding='utf-8').read(), re.M)
        return f'（[原典 PDF]({m.group(1)})）' if m else ''
    def note(n): return notes_md.note_body(f'{P}/notes/{n}.md', skip=('[', '照合先'))
    by_mod = collections.defaultdict(list)
    for r in keep: by_mod['.'.join(r['section'].split('.')[:2])].append(r)
    # 項目を載せない小節・節にも原稿（NB-W3 (b) の転記など）があれば見出しを立てる
    extra = collections.defaultdict(set)
    for fp in glob.glob(f'{P}/notes/*.md'):
        n = os.path.basename(fp)[:-3]
        if n in rev or n == 'README': continue
        extra['.'.join(n.split('.')[:2])].add(n)
        by_mod.setdefault('.'.join(n.split('.')[:2]), [])
    stats = collections.Counter(); modules = []
    for sec in sorted(by_mod, key=skey):
        imports = set(); body = []
        subs = collections.defaultdict(list)
        for r in by_mod[sec]: subs[r['section'] if r['section'].count('.') >= 2 and not r['section'].endswith('.0') else sec].append(r)
        for n in extra[sec]:
            if n != sec: subs.setdefault(n, [])
        for sub in sorted(subs, key=skey):
            if sub != sec:
                body.append(f'# {sub} {esc(heads.get(sub, ""))}\n')
                body.append('%%%\nnumber := false\ntag := "' + f'{key}-' + slug(sub).replace('_', '-') + '"\n%%%\n')
                if (nb := note(sub)): body.append(nb); stats['with-note-intro'] += 1
            for r in sorted(subs[sub], key=lambda r: skey(r['number'])):
                n = r['number']; rv = rev[n]; st = rv.get('status') or 'none'
                linked = res.links(label(key, n), rv.get('declarations', ''), imports, True)
                stats[st] += 1; stats['linked' if linked else 'nolink'] += 1
                opts = f' (lean := "{", ".join(linked)}")' if linked else ''
                if (us := USES.get((abbr, n))): opts += f' (uses := "{", ".join(us)}")'; stats['with-uses'] += 1
                pk = rv.get('partial_kind', '')
                state = STATUS.get(st, st) + (f'（{pk}）' if st == 'partial' and pk else '')
                ttl = re.sub(r'<[^>]+>', '', r.get('title') or '')
                body.append(f':::{KIND.get(r["kind"], "proposition")} "{label(key, n)}"{opts}')
                body.append(f'*{abbr} {KINDJA.get(r["kind"], esc(r["kind"]))} {esc(n)}*' + (f'　{esc(ttl)}' if ttl else '') + pdf(n) + f'。対応表の状態：{state}。\n')
                if n in STMT: body.append(STMT[n]); stats['with-statement'] += 1
                if rv.get('reason'): body.append(esc(rv['reason']) + '\n')
                if (nb := note(n)): body.append(nb); stats['with-note'] += 1
                if declaration_note := res.declaration_note(label(key, n), rv.get('declarations', ''), linked): body.append(declaration_note)
                body.append(':::\n')
        mod = f'Section{slug(sec)}'
        ch = sec.split('.')[0]
        hd = heads.get(sec) or (heads.get(ch, '') + '（章の導入）' if sec.endswith('.0') or sec == ch else '')
        if sec == '0': hd = '序論'
        hd = re.sub(r'[][]', '', hd)
        hdr = ['import Verso', 'import VersoManual', 'import VersoBlueprint'] + [f'import {m}' for m in sorted(imports)] + \
              ['', 'open Verso.Genre', 'open Verso.Genre.Manual', 'open Informal', '', '-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）', 'set_option maxHeartbeats 2000000', '',
               f'#doc (Manual) "{abbr} {sec} {hd}" =>', '%%%', 'number := false', f'tag := "{key}-{slug(sec).replace("_", "-")}"', '%%%', '',
               f'{abbr} {sec} の項目のうち、本体か Mathlib に対応があるもの（対応表 `research/{key}-coverage` の状態が「なし」でないもの）。本文は日本語で独立に書いた要約と解説で、原典の本文の写しではない。\n']
        if (nb := note(sec)): hdr.append(nb); stats['with-note-intro'] += 1
        res.write(f'{OUT}/{mod}.lean', '\n'.join(hdr + body) + '\n')
        modules.append(mod)
    json.dump({'key': key, 'dir': dirname, 'title': title, 'modules': modules, 'stats': dict(stats)},
              open(f'{OUT}/generated.json', 'w'), ensure_ascii=False, indent=1)
    print(key, len(modules), 'sections', dict(stats))
if __name__ == '__main__':
    for k in sys.argv[1:]: gen(k)
