"""概念の木 版 6 の割り当て（2026-11-20 の決定 decisions-2026-11-20.md による）。
使い方：python3 assign6.py <W.pkl> <X.pkl> <trunk5.pkl> <出力の接頭辞> <出力の pickle>

規則：
- 核は本体の全ての定義（定理でない宣言。instance は除く）。読んだ定義は、読んだ結果を移し替えの表（remap/remap-*.csv）に通した概念・小概念。
  読んでいない定義は、下の宣言と同じ規則で、自分の主張（なければ本体）から決める。
- 概念の上下：B の定義が A の定義を使って作られていれば A が土台。B の定義のうち A の定義を使うものが 5% 以上で、逆向きの 2 倍を超えるとき、A を B の土台とする（推移的に閉じる）。
- 宣言：主張に現れる定義の概念の集合から、土台になっている概念を除く。残りが一つならその概念（小概念は、その概念の定義のうち主張に現れる最も深いもの）。
  複数残れば、段の最も高い概念の下の小概念「〈相手〉との関係」。主張に本体の定義が現れなければ、Mathlib の定義の規則。
- 印：補助（読む作業で足場とされた定義を主張に含む）、止めた経路（表の印、またはファイルの冒頭に「中断」とある）。"""
import pickle, re, sys, collections, csv, os, json, glob
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from trunk import MATHLIB_ROOTS, MATHLIB_ROOTS3, RENAME
W = pickle.load(open(sys.argv[1], 'rb')); N = W['N']; xn, X = pickle.load(open(sys.argv[2], 'rb')); T5 = pickle.load(open(sys.argv[3], 'rb'))
PRE, OUTP = sys.argv[4], sys.argv[5]
A_ = 'A 可換代数と数論幾何/'
# 調整役の上書き（2026-11-20）：Adams 作用素を概念に、Tor と対角線は交点重複度と χ へ、名前の直し
CREN = {A_ + 'Hilbert–Samuel と対角線': A_ + 'Hilbert–Samuel 関数', A_ + 'スキーム': A_ + 'スキーム（有限表示の模型による近似と降下）'}
def override(c, s):
    if 'Adams' in s or '一元 Koszul 複体のテンソル冪' in s: return A_ + 'Adams 作用素', 'Adams 作用素の計算（一元 Koszul 複体のテンソル冪の模型）'
    if s == 'Tor 加群' or s.startswith('対角線の環'): return A_ + '交点重複度と χ', s
    if s == '複体の標準 fiber と引き戻し四角形': s = '複体の dg 神経での fiber 四角形と cofiber 四角形'
    return CREN.get(c, c), s
# 移し替えの表
REMAP = {}; byold = collections.defaultdict(collections.Counter)
for f in sorted(glob.glob(os.path.join(HERE, 'remap', 'remap-*.csv'))):
    for r in csv.DictReader(open(f, encoding='utf-8')):
        c, s = override(r['new_concept'], r['new_subconcept'])
        old = r['group'] + '/' + r['concept']
        REMAP[(old, r['subconcept'])] = (c, s, r['aux'] == '1', r['stopped'])
        byold[old][c] += 1
CMAP = {}
for old, cnt in byold.items():
    for k in ('（読んで移した定義）', '（まだ読んでいない定義）', '（Mathlib の定義だけの主張）', '（その他）'):
        if (old, k) in REMAP: CMAP[old] = REMAP[(old, k)][0]; break
    else: CMAP[old] = cnt.most_common(1)[0][0]
norm = lambda c: RENAME.get(c, c)
def remap(c_old, s_old):
    c_old = norm(c_old)
    if (c_old, s_old) in REMAP: return REMAP[(c_old, s_old)]
    return (CMAP.get(c_old, CREN.get(c_old, c_old)), '', False, '')
# 読んだ定義
READ = {}
for h, s in T5['SUB'].items():
    c, sb, aux, stp = remap(T5['L'][h], s)
    READ[h] = (c, sb if not sb.startswith('（') else '', aux, stp)
# Mathlib の根と小概念の規則
MR = [(c, re.compile(p)) for c, p in MATHLIB_ROOTS3 + MATHLIB_ROOTS]
xroot = {}
for q, n in xn.items():
    for i, (c, p) in enumerate(MR):
        if p.search(n): xroot[q] = (i, c); break
MRULES = {}
for f in glob.glob(os.path.join(HERE, 'split', 'c*.json')):
    j = json.load(open(f, encoding='utf-8'))
    if j.get('mathlib_rules'): MRULES[norm(j['concept'])] = [(re.compile(r), n) for r, n in j['mathlib_rules']]
def mathlib_assign(x):
    xs = [xroot[q] for q in X.get(x, ()) if q in xroot]
    if not xs: return None
    c_old = norm(min(xs)[1]); s_old = '（Mathlib の定義だけの主張）'
    if c_old in MRULES:
        names = [xn[q] for q in X.get(x, ())]
        for r, nm in MRULES[c_old]:
            if any(r.search(n0) for n0 in names): s_old = nm; break
    c, sb, aux, stp = remap(c_old, s_old)
    return c, ('' if sb.startswith('（') else sb)
# 止めた経路：ファイルの冒頭
STOPMOD = {}
def stopped_mod(m):
    if m not in STOPMOD:
        try: head = ''.join(open(m.replace('.', '/') + '.lean', encoding='utf-8').readlines()[:40])
        except Exception: head = ''
        k = re.search(r'中断[^\n。]{0,40}', head)
        STOPMOD[m] = ('任意のモデル圏への一般化（計画書 §396）' if '任意モデル源' in head and '中断' in head else (k.group(0) if k and '分類B' in head else '')) if k else ''
    return STOPMOD[m]
# 位相順
indeg = {h: len(d['tdeps']) + len(d['vdeps']) for h, d in N.items()}
order = []; st = [h for h, k in indeg.items() if k == 0]
while st:
    x = st.pop(); order.append(x)
    for u in N[x]['users']:
        indeg[u] -= 1
        if indeg[u] == 0: st.append(u)
depth = {}
for x in order: depth[x] = 1 + max([depth[q] for q in N[x]['tdeps'] | N[x]['vdeps']], default=-1)
ishub = lambda d: d['kind'] != 'thm' and not d['inst']
def run(UP, LEVEL):
    con = {}; sub = {}; how = {}; aux = {}; cset = {}
    def decide(cs, hubs):
        # cs: 概念の集合、hubs: (深さ, 概念, 小概念, 補助) の列
        mx = [c for c in cs if not any(c in UP.get(o, ()) for o in cs if o != c)]
        if not mx: mx = sorted(cs)
        if len(mx) == 1:
            c = mx[0]; hs = sorted([h for h in hubs if h[1] == c], reverse=True)
            sb = next((h[2] for h in hs if h[2]), ''); return c, sb, bool(hs and hs[0][3]), '一つ'
        mx.sort(key=lambda c: (-LEVEL.get(c, 0), c)); c = mx[0]
        return c, '〈' + '・'.join(o.split('/', 1)[1] for o in mx[1:3]) + ('ほか' if len(mx) > 3 else '') + '〉との関係', False, '関係'
    for x in order:
        d = N[x]
        if x in READ:
            c, sb, a, stp = READ[x]; con[x], sub[x], aux[x], how[x] = c, sb, a, '読んだ定義'; cset[x] = (c,); continue
        for deps, tag in ((d['tdeps'], '主張'), (d['vdeps'] if d['kind'] != 'thm' else (), '本体')):
            hubs = [(depth[q], con[q], sub.get(q, ''), aux.get(q, False)) for q in deps if ishub(N[q]) and con.get(q)]
            if hubs:
                cs = {h[1] for h in hubs}; c, sb, a, kind = decide(cs, hubs)
                con[x], sub[x], aux[x], how[x] = c, sb, a, f'{tag}：{kind}'; cset[x] = tuple(sorted(cs)); break
        else:
            m = mathlib_assign(x)
            if m: con[x], sub[x], aux[x], how[x] = m[0], m[1], False, 'Mathlib の定義'; cset[x] = ()
            else:
                cs = [con[q] for q in d['tdeps'] | d['vdeps'] if con.get(q)]
                if cs: con[x], sub[x], aux[x], how[x] = collections.Counter(cs).most_common(1)[0][0], '', False, '証明から'; cset[x] = ()
                else: con[x], sub[x], aux[x], how[x] = None, '', False, '未割り当て'; cset[x] = ()
    return con, sub, how, aux, cset
def concept_order(con):
    size = collections.Counter(); E = collections.Counter()
    for x, d in N.items():
        if not ishub(d) or not con.get(x): continue
        a = con[x]; size[a] += 1
        for b in {con.get(q) for q in d['tdeps'] | d['vdeps'] if ishub(N[q])} - {a, None}: E[(a, b)] += 1
    up = collections.defaultdict(set)
    for (a, b), k in E.items():
        if k / size[a] >= 0.05 and k / size[a] > 2 * E.get((b, a), 0) / size[b]: up[a].add(b)
    def anc(a, seen):
        for b in up.get(a, ()):
            if b not in seen: seen.add(b); anc(b, seen)
        return seen
    UP = {a: anc(a, set()) - {a} for a in size}; LEVEL = {}
    def lv(a, stack=()):
        if a in LEVEL: return LEVEL[a]
        if a in stack: return 0
        LEVEL[a] = 1 + max([lv(b, stack + (a,)) for b in up.get(a, ())], default=-1); return LEVEL[a]
    for a in size: lv(a)
    return UP, LEVEL, E, size
# 一回目：読んだ定義だけから上下を出す → 全体を割り当て → 二回目：全ての定義から上下を出し直す
con0 = {h: v[0] for h, v in READ.items()}
UP, LEVEL, _, _ = concept_order(con0)
con, sub, how, aux, cset = run(UP, LEVEL)
# 上下は読んだ定義だけから出す（読んでいない定義の割り当てを入れて出し直すと、割り当ての誤りが上下に入り込む。確認 2 回目で S 構成の入力と S 構成、塔と Postnikov が逆になっていた）
# 読んだ定義だけでは上下の付かない組が多く、「関係」が 14% に膨らむ（読んだ側が関係としたのは 2〜3%）。
# そこで、読んだ定義から出た上下を正とし、それと矛盾しない範囲で、全ての定義から出した上下を足す。
UPr = UP
if not os.environ.get('ORDER_READ_ONLY'):
    ca = con
    for it in range(2):
        UPa, _, _, _ = concept_order(ca)
        UPm = {}
        for a0 in set(UPr) | set(UPa):
            UPm[a0] = set(UPr.get(a0, ())) | {b for b in UPa.get(a0, ()) if a0 not in UPr.get(b, ()) and b not in UPr.get(a0, ()) and not any(a0 in UPr.get(m, ()) for m in [b])}
        LEVELm = {}
        def lvm(a1, stack=()):
            if a1 in LEVELm: return LEVELm[a1]
            if a1 in stack: return 0
            LEVELm[a1] = 1 + max([lvm(b, stack + (a1,)) for b in UPm.get(a1, ())], default=-1); return LEVELm[a1]
        for a1 in UPm: lvm(a1)
        UP, LEVEL = UPm, LEVELm
        con, sub, how, aux, cset = run(UP, LEVEL); ca = con
_, _, E, size = concept_order(con0)
stopped = {}
for x, d in N.items():
    s = READ[x][3] if x in READ else ''
    stopped[x] = s or stopped_mod(d['mod'])
print(collections.Counter(re.sub(r'：.*', '', h) + ('：' + h.split('：')[1] if '：' in h else '') for h in how.values()))
print('concepts', len({c for c in con.values() if c}), 'aux', sum(aux.values()), 'stopped', sum(1 for v in stopped.values() if v), 'unassigned', sum(1 for c in con.values() if not c))
KS = ['結果', '再利用', '分割', '言い換え', '未使用']
T = collections.defaultdict(collections.Counter)
for x, d in N.items():
    k = T[(con[x] or '（未割り当て）/（未割り当て）', sub[x] or '（小概念なし）')]
    k['decls'] += 1; k['lines'] += d['lines']; k['layer%d' % d['layer']] += 1; k[d['K']] += 1; k['aux'] += aux[x]; k['stopped'] += bool(stopped[x]); k['relation'] += how[x].endswith('関係')
cols = ['decls', 'lines', 'layer1', 'layer2', 'layer3', 'layer4'] + KS + ['aux', 'stopped']
with open(PRE + '-sub.csv', 'w', encoding='utf-8') as f:
    w = csv.writer(f); w.writerow(['group', 'concept', 'subconcept', 'level'] + cols)
    for (c, sb) in sorted(T): w.writerow(c.split('/', 1) + [sb, LEVEL.get(c, '')] + [T[(c, sb)][k] for k in cols])
with open(PRE + '-order.csv', 'w', encoding='utf-8') as f:
    w = csv.writer(f); w.writerow(['concept', 'level', 'definitions', 'built_on'])
    for c in sorted({c for c in con.values() if c}, key=lambda c: (LEVEL.get(c, 0), c)):
        direct = sorted(((E[(c, b)] / size[c], b) for b in UP.get(c, ()) if size.get(c) and E.get((c, b), 0) / size[c] >= 0.05), reverse=True)
        w.writerow([c, LEVEL.get(c, 0), size.get(c, 0), '、'.join(f"{b.split('/', 1)[1]} {p * 100:.0f}%" for p, b in direct[:6])])
pickle.dump(dict(con=con, sub=sub, how=how, aux=aux, stopped=stopped, cset=cset, UP={k: sorted(v) for k, v in UP.items()}, LEVEL=LEVEL, E=E, size=size), open(OUTP, 'wb'))
st = collections.Counter()
for (c, sb), k in T.items():
    key = '関係' if sb.endswith('との関係') else '小概念なし' if sb == '（小概念なし）' else '小概念'
    st[key] += k['decls']
print(dict(st), 'subconcepts', sum(1 for (c, sb) in T if not sb.startswith('（') and not sb.endswith('との関係')), 'relations', sum(1 for (c, sb) in T if sb.endswith('との関係')))
