import sys,collections,json,pickle,re; S=sys.argv[1]; sys.path.insert(0,S+'/zero'); from lib import sh,clos
N,HUB=pickle.load(open(f'{S}/zero/G.pkl','rb'))
ext=json.load(open(f'{S}/zero/ext.json'))
KJ={'def':'定義','struct':'構造','inst':'インスタンス','thm':'定理'}
out=[]
W=out.append
W('# 見本の範囲の宣言の整理（ファイルを使わない版、第 1 稿）\n')
W('2026-11-20、調整役。main `cf88139c3` の手前（`1cb048402`）のビルド済みの環境から、`SerrePositivity/Spectra/General/` と `SerrePositivity/LengthAlgebra/` の全宣言 1,058 件を書き出して作った。Lean のソースは変えていない。\n')
W('## 作り方\n')
W('1. 宣言ごとに、主張（型）の中で使う宣言と、証明・中身の中で使う宣言を Lean から採る。')
W('2. 自動生成の宣言（`_proof_1`、`eq_1`、`@[reassoc]` の `_assoc` など）は、元の宣言に畳む。')
W('3. 要の定義（多くの宣言が頼る定義）を選び、グループの名前を付ける。ここだけが人の判断。')
W('4. 各宣言を、それが直接・間接に頼る要の定義のうち、一番上のグループに入れる。今あるファイルは使わない。')
W('5. 「ファイル」の列は、今の置き場所を引くためだけに付けてある。\n')
def pairs(A):
    names={sh(p).lower():p for p in A}
    out=[]
    for p in A:
        s=sh(p)
        if 'otensor' in s:
            t=re.sub('cotensor','tensor',re.sub('Cotensor','Tensor',s))
            if t!=s and t.lower() in names: out.append((p,names[t.lower()]))
    return out
for area,title in [('Spectra','Spectra/General'),('LengthAlgebra','LengthAlgebra')]:
    hs=HUB[area]; A={p:d for p,d in N.items() if d['area']==area}
    W(f'\n## {title}（畳んだ後 {len(A)} 件）\n')
    W('### グループと、グループどうしの依存\n')
    W('| 番号 | グループ | 宣言 | 定義 | 定理 | 行 | 頼るグループ | 今のファイル数 |\n| ---: | --- | ---: | ---: | ---: | ---: | --- | ---: |')
    order=list(range(len(hs)))+[-1]
    lab=lambda i: hs[i][0] if i>=0 else '（範囲の定義に頼らない）'
    for i in order:
        M={p:d for p,d in A.items() if d['g']==i}
        if not M: continue
        k=collections.Counter(d['kind'] for d in M.values())
        below=sorted({N[q]['g'] for d in M.values() for q in d['ti']|d['vi'] if N[q]['g']!=i and N[q]['g']>=0})
        W(f"| {i if i>=0 else '—'} | {lab(i)} | {len(M)} | {k['def']+k['struct']+k['inst']} | {k['thm']} | {sum(d['lines'] for d in M.values())} | {'、'.join(map(str,below)) or '—'} | {len({d['file'] for d in M.values()})} |")
    fg=collections.defaultdict(set)
    for d in A.values(): fg[d['file']].add(d['g'])
    W(f"\n今のファイル {len(fg)} 本のうち、二つ以上のグループの宣言が混ざっているものは {sum(1 for v in fg.values() if len(v)>1)} 本。\n")
    W('### 手を入れる候補\n')
    nowhere=[p for p in A if not A[p]['users'] and ext.get(p,[1,1])==[0,0]]
    one=[p for p in A if len(A[p]['users'])==1 and A[p]['kind']=='thm']
    oned=[p for p in A if len(A[p]['users'])==1 and A[p]['kind']!='thm']
    law=[p for p in A if A[p]['isdef'] and A[p]['type'].strip().endswith('Prop') and p.endswith('Law')]
    ty=collections.defaultdict(list)
    for p,d in A.items():
        if d['kind']=='inst' or 'inst' in p.split('.')[-1][:4]: ty[re.sub(r'\s+',' ',d['type'])].append(p)
    dupi=[v for v in ty.values() if len(v)>1]
    pr=pairs(A)
    free=[p for p in A if A[p]['g']==-1]
    W('| 候補 | 件数 | 行 |\n| --- | ---: | ---: |')
    L=lambda ps: sum(A[p]['lines'] for p in ps)
    W(f"| どこからも使われない（範囲内・範囲外・対応表のどれにも出ない） | {len(nowhere)} | {L(nowhere)} |")
    W(f"| 範囲内で一か所からしか使われない定理 | {len(one)} | {L(one)} |")
    W(f"| 範囲内で一か所からしか使われない定義・インスタンス | {len(oned)} | {L(oned)} |")
    W(f"| 補題の主張に名前を付けただけの定義（〜Law） | {len(law)} | {L(law)} |")
    W(f"| 同じ型のインスタンスの重複 | {sum(len(v) for v in dupi)}（{len(dupi)} 組） | {L([p for v in dupi for p in v])} |")
    W(f"| tensor／cotensor で名前が対になる宣言 | {len(pr)} 組 | {L([x for a,b in pr for x in (a,b)])} |")
    W(f"| 範囲の定義に頼らない宣言 | {len(free)} | {L(free)} |")
    W('\n「一か所からしか使われない」は範囲内の数。範囲の外からの使用は、この稿では数えていない。\n')
    def lst(ps,extra=lambda p:''):
        for p in sorted(ps,key=lambda p:(A[p]['g'],A[p]['file'],p)):
            W(f"- `{sh(p)}`（{KJ[A[p]['kind']]}、{A[p]['lines']} 行、{A[p]['file']}）{extra(p)}")
    W('<details><summary>どこからも使われない宣言</summary>\n'); lst(nowhere); W('\n</details>\n')
    if law:
        W('<details><summary>〜Law の定義</summary>\n'); lst(law,lambda p:' ← '+('、'.join('`'+sh(q)+'`' for q in sorted(A[p]['tusers'])[:3]) or 'なし')); W('\n</details>\n')
    if dupi:
        W('<details><summary>同じ型のインスタンス</summary>\n')
        for v in dupi:
            W(f"- 型：`{re.sub(chr(10),' ',A[v[0]]['type'])[:160]}`"); 
            for p in v: W(f"  - `{sh(p)}`（{A[p]['file']}）")
        W('\n</details>\n')
    if pr:
        W('<details><summary>tensor／cotensor の対</summary>\n')
        for a,b in sorted(pr): W(f"- `{sh(b)}`（{A[b]['lines']} 行） ／ `{sh(a)}`（{A[a]['lines']} 行）")
        W('\n</details>\n')
    if free:
        W('<details><summary>範囲の定義に頼らない宣言</summary>\n')
        lst(free,lambda p:'　主張に出る範囲外の本体の定義：'+('、'.join('`'+x.replace('SerrePositivity.','')+'`' for x in sorted(A[p]['ext_t']) if x.startswith('SerrePositivity'))[:200] or 'なし（Mathlib だけ）'))
        W('\n</details>\n')
    W('### グループごとの全宣言\n')
    W('「頼られる数」は、その宣言に直接・間接に頼る範囲内の宣言の数。「使う所」は直接使う範囲内の宣言の数。\n')
    for i in order:
        M={p:d for p,d in A.items() if d['g']==i}
        if not M: continue
        W(f"<details><summary>{i if i>=0 else '—'}　{lab(i)}（{len(M)} 件）</summary>\n")
        W('| 宣言 | 種類 | 行 | 頼られる数 | 使う所 | ファイル | 説明（docstring の頭） |\n| --- | --- | ---: | ---: | ---: | --- | --- |')
        for p,d in sorted(M.items(),key=lambda kv:(kv[1]['kind']=='thm',-len(clos(N,kv[0])),kv[0])):
            doc=re.sub(r'\s+',' ',d['doc'])[:60].replace('|','/')
            W(f"| `{sh(p)}` | {KJ[d['kind']]} | {d['lines']} | {len(clos(N,p))} | {len(d['users'])} | {d['file']} | {doc} |")
        W('\n</details>\n')
open('research/cleanup-zero-base/pilot-first-draft.md','w').write('\n'.join(out)+'\n')
print(len(out))
