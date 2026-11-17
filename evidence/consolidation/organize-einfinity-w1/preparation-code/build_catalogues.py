"""Build the OE-W1 per-file catalogues from real source headers, without proof bodies."""
from pathlib import Path
from collections import Counter
import argparse,csv,json,re,sys,gzip
from source_names import declarations
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--applied',action='store_true');p.add_argument('--owners',type=Path);a=p.parse_args();root=a.root.resolve();base=root/'evidence/consolidation/organize-einfinity-w1';rows=list(csv.DictReader((base/'stage1-modules.csv').open()));linkroot='/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-bs-d68'

if a.applied and not a.owners:p.error('--applied requires observed after-owner inventory')
owner_file=a.owners or base/'preparation/native-owners-before.json.gz'
owner_data=json.loads(gzip.open(owner_file,'rt').read() if owner_file.suffix=='.gz' else owner_file.read_text())
owned={(r['module'],r['name']) for r in owner_data['declarations'] if not r['is_private']}
owner_counts=Counter(r['module'] for r in owner_data['declarations'])

def header(source,line):
 # Stop at the body marker outside all brackets, comments, and string literals.
 text='\n'.join(source.splitlines()[line-1:]);depth=0;comment=0;string=False;i=0
 while i<len(text):
  if comment:
   if text.startswith('/-',i):comment+=1;i+=2;continue
   if text.startswith('-/',i):comment-=1;i+=2;continue
   i+=1;continue
  if string:
   if text[i]=='\\':i+=2;continue
   if text[i]=='"':string=False
   i+=1;continue
  if text.startswith('/-',i):comment=1;i+=2;continue
  if text.startswith('--',i):
   n=text.find('\n',i);i=len(text) if n<0 else n;continue
  if text[i]=='"':string=True;i+=1;continue
  if not depth and (text.startswith(':=',i) or re.match(r'where\b',text[i:])):return text[:i].rstrip()
  if text[i] in '([{⦃':depth+=1
  elif text[i] in ')]}⦄':depth-=1
  if i>12000:raise ValueError('Header too long or no body marker')
  i+=1
 return text.rstrip()

def context(source,line):
 lines=source.splitlines()[:line-1];out=[];active=False
 for s in lines:
  start=bool(re.match(r'^(universe|variable)\b',s))
  if start or active and s.startswith((' ','\t')):out.append(s);active=True
  else:active=False
 return '\n'.join(out)
for be in (False,True):
 selected=[r for r in rows if (r['id']=='OE05')==be];folder='is-w2-be-route' if be else 'einfinity-general';out=a.output/folder/'README.md';out.parent.mkdir(parents=True,exist_ok=True)
 text=['# '+('D81で止めたIS-W2 BE Tot経路の部品目録' if be else 'EInfinityから分離する一般のホモトピー論・∞圏論の部品目録'),'','OE-W1、2026-11-16。基準main `30ae8948f339beec42d9340feb02f2031c22c72b`。','',f"対象は **{len(selected)}ファイル・{sum(int(r['lines']) for r in selected):,}原Lean行**。",
 '', '## 状態・検証の出所','',
 ('この経路はD81で停止。CAlgはHA流で構成する方針に変わった。BE模型に固定した既存の型と到達点を保管し、実装を再開しない。IS-W2の一覧は12/25が済み、R03d・R03hとTot全体の比較は未完、実現側R06〜R10は未着手。一般部品の目録とHA Monadsの既存目録も参照する。' if be else 'ここにまとめるのは一般の図式・重み・frame・局所化の部品。SSetのモデル構造を全域で仮定するという意味ではなく、各型の仮定に従う。一般の複体・模型圏の定理と、具体的なBE値の比較を区別する。'),'',
 '**準備中**：現在の抜粋は基準ソースの実際の宣言ヘッダー。移動後の対象ビルド・v3b・引用／タグ・root・正式全監査・verifyは未検収。最終の検査結果はreport-organize-einfinity.mdを正本とし、完了を先取りしない。' if not a.applied else '抜粋は移動後ソースの実際の宣言ヘッダー。検証の完了状況はreport-organize-einfinity.mdを参照する。','',
 '## 読み方・原典・入力','',
 '各ファイルの概要・方針・規約・利用箇所はmodule docstringから抜き出した。原典番号は利用箇所の説明であり、その一般定理の完成を意味しない。型はnative所有元と名前の実在を確認できた公開ソース宣言から証明本体を除いた抜粋。局所のuniverse・variable文脈を併記するが、open・記法・local instance・import・sectionの範囲はリンク先を参照する。ここを連結してLeanへ貼る用途ではない。','',
 '配置上の対応：Kerodonはタグに対応する章・節、HA §1.3.4は模型圏の局所化、HomotopicalAlgebraは図式の重みとホモトピー関数複体。HA Monadsの179本は今回移動せず、既存の research/g12-monad-route/README.md を参照する。','',
 '## 役割別の集計','', '| 束 | ファイル | 原Lean行 |','|---|---:|---:|']
 for ident in sorted({r['id'] for r in selected}):
  xs=[r for r in selected if r['id']==ident];text.append(f"| {ident} | {len(xs)} | {sum(int(r['lines']) for r in xs):,} |")
 text+=['','## ファイルごとの構成と型','']
 for r in sorted(selected,key=lambda r:(r['id'],r['new_path'])):
  path=r['new_path'] if a.applied else r['old_path'];source=(root/path).read_text();module=r['new_module'] if a.applied else r['old_module'];ds=[d for d in declarations(source,path) if (module,d[0]) in owned];doc=re.search(r'/\-!\s*(.*?)\n-/',source,re.S)
  text += [f"### [{Path(path).name}]({linkroot}/{path})",'',f"{r['id']}、{r['lines']}原行。配置：`{r['new_module']}`。",'',doc[1].strip() if doc else 'module docstringなし。実際の型とimportを参照。','']
  if ds:
   name,_,line=ds[0];ctx=context(source,line);snippet=header(source,line);text += [f'主宣言（基準の完全名）：`{name}`。' if not a.applied else f'主宣言：`{name}`。','','```lean',*( [ctx,''] if ctx else []),snippet,'```','']
  else:text += [f'native所有元表には{owner_counts[module]}宣言。抜粋対象の名前つき公開ソース宣言なし（import用、匿名instance、生成宣言など）。原ソースと全native表を参照。','']
 out.write_text('\n'.join(text).rstrip()+'\n')
 print(folder,len(selected),sum(int(r['lines']) for r in selected),len(text))
