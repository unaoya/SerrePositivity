#!/usr/bin/env python3
"""豊穣化を作っている宣言の候補を挙げる（調整役の下調べ）。
  python3 research/cleanup-zero-base/enrichment/constructions.py <audit.sqlite> <出力 csv>
記録監査の宣言の表から、型に豊穣の概念が現れる定義を取り、ソースの宣言の頭を読んで、結論の型が豊穣の構造であるものを「作っている」とする。
やり方（直接／作用から／基底の取り替え）は、本体が直接使っている定数から仮に付ける（読んで確かめる前の目印）。"""
import sys, sqlite3, json, re, csv, collections, os
DB, OUT = sys.argv[1], sys.argv[2]
HEADS = ['EnrichedCategory', 'EnrichedOrdinaryCategory', 'SimplicialCategory', 'TensorCotensor', 'EnrichedRepresentability', 'TransportEnrichment', 'DGCategory', 'SimplicialTensorCotensor']
con = sqlite3.connect(DB)
rows = con.execute("select name,module,kind,location,type_refs,value_refs,instances from decl where internal=0 and kind='def'").fetchall()
src = {}
def text(mod, loc):
    p = mod.replace('.', '/') + '.lean'
    if p not in src:
        src[p] = open(p, encoding='utf-8').read().split('\n') if os.path.exists(p) else []
    L = src[p]; a = loc[0] - 1; b = min(loc[2], a + 40)
    return '\n'.join(L[a:b])
out = []
for name, mod, kind, loc, tr, vr, inst in rows:
    tr = json.loads(tr)
    if not any(any(h in t.split('.') for h in HEADS) for t in tr): continue
    if not loc: continue
    t = text(mod, json.loads(loc))
    head = re.split(r':=|\bwhere\b', t, 1)[0]
    # 結論の型：括弧の外の最後のコロンの後
    depth = 0; last = -1
    for i, ch in enumerate(head):
        if ch in '([{⦃': depth += 1
        elif ch in ')]}⦄': depth -= 1
        elif ch == ':' and depth == 0 and head[i:i+2] != ':=': last = i
    concl = head[last + 1:].strip() if last >= 0 else ''
    m = re.match(r'(?:@)?((?:\w+\.)*)(\w+)', concl)
    h = m.group(2) if m else ''
    if h not in HEADS: continue
    vr = json.loads(vr or '[]')
    vs = ' '.join(vr)
    how = []
    if 'TransportEnrichment' in vs or 'TransportEnrichment' in ' '.join(tr): how.append('基底の取り替え（Mathlib）')
    if 'LaxPointHom' in vs or 'Enriched.Transport' in vs: how.append('基底の取り替え（本体）')
    if 'RepresentedMappingEnrichment' in vs or 'MappingUnitLaws' in vs: how.append('作用から（本体）')
    if 'enrichedCategorySelf' in vs or 'enrichedOrdinaryCategorySelf' in vs: how.append('自己豊穣化（Mathlib）')
    if re.search(r'EnrichedCategory\.mk|EnrichedOrdinaryCategory\.mk|SimplicialCategory\.mk', vs) and not how: how.append('直接')
    out.append({'declaration': name, 'module': mod.replace('SerrePositivity.', ''), 'area': '/'.join(mod.split('.')[1:3]), 'result': h,
                'instance': 'yes' if inst and inst != '[]' else '', 'lines': json.loads(loc)[2] - json.loads(loc)[0] + 1,
                'how_guess': ' | '.join(how) or '？', 'conclusion': ' '.join(concl.split())[:200]})
out.sort(key=lambda r: (r['area'], r['module'], r['declaration']))
with open(OUT, 'w', encoding='utf-8', newline='') as f:
    w = csv.DictWriter(f, fieldnames=list(out[0].keys())); w.writeheader(); w.writerows(out)
print(len(out))
print(collections.Counter(r['result'] for r in out))
print(collections.Counter(r['how_guess'] for r in out))
for a, n in collections.Counter(r['area'] for r in out).most_common(): print(n, a)
