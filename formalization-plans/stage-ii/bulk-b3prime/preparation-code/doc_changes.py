from pathlib import Path
import json,re,sys,hashlib
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');W=Path('/tmp/bulk-b3prime');sys.path.insert(0,str(W));from doc_plan import comments
# All transforms apply inside comments only. Attribute strings and Lean tokens are never changed.
LABELS={'G9-4':'還元と余核の比較','G9':'離散性の判定','G8':'係数制限と完備化の比較','G7':'余極限との比較','G4':'ghost 成分の単射性の補題','D5b':'離散代数の埋め込み','D3':'導来ホモトピー圏の比較','D6a':'ホモトピー引き戻しの長完全列','D4':'導来テンソル積の比較','Π2-5':'普遍単位と指定錐の比較','Π2-6':'整代数の離散性と普遍性','Π2-7':'環の excision の比較','Π2':'界面から得る環の定理'}
def update(comment,path):
 comment=re.sub(r'André E[123]：','André：',comment)
 for a,b in [('D36 で用いる p 正則な部分圏','p 正則な部分圏'),('の D36 の評価範囲','の p 正則な対象の評価範囲'),('の D36 の範囲','の p 正則な対象の範囲'),('評価射の範囲は D36。','評価射は p 正則な対象上で扱う。'),('（D36）',''),('と D76',''),('D76 の入力','有界な関係商の入力'),('D76 の有界性','関係商の有界性'),('（D4-02）',''),('（ω 段、D51）','（可算塔）')]:comment=comment.replace(a,b)
 for token,new in sorted(LABELS.items(),key=lambda pair:len(pair[0]),reverse=True):comment=re.sub(r'(?<![A-Za-z0-9_])'+re.escape(token)+r'(?![A-Za-z0-9_.-])',lambda _:new,comment)
 g10='prismatic な包絡の比較' if '/Semiperfectoid/' in path else '冪零還元からの純性・平坦性の判定'
 comment=re.sub(r'(?<![A-Za-z0-9_])G10(?![A-Za-z0-9_.-])',g10,comment)
 if '/Perfectoidization/' in path or '/Almost/' in path:
  comment=re.sub(r'(?<![A-Za-z0-9_])E3(?![A-Za-z0-9_.-])','導来 perfectoid 化の界面',comment)
 elif '/Semiperfectoid/' in path:
  comment=re.sub(r'(?<![A-Za-z0-9_])E3(?![A-Za-z0-9_.-])','任意添字の包絡の構成',comment)
 comment=re.sub(r'\bexisting G2\s+principal','existing principal',comment);comment=re.sub(r'\bG2 comparison\b','completion comparison',comment);comment=re.sub(r'\bG2 completed\b','completed',comment)
 return comment
rows=[]
for root in ['Semiperfectoid','Andre','Perfectoidization','Almost','PerfectoidIdeal','IntegralPerfectoidization']:
 for p in (R/'SerrePositivity/BhattScholze'/root).rglob('*.lean'):
  text=p.read_text();path=p.relative_to(R).as_posix()
  for a,b in comments(text):
   old=text[a:b];new=update(old,path)
   if old!=new:rows.append({'path':path,'start':a,'stop':b,'source_sha256':hashlib.sha256(text.encode()).hexdigest(),'before':old,'after':new})
# Preview text only; do not write any Lean file while original-environment captures run.
(W/'doc-change-proposals.json').write_text(json.dumps({'status':'comment-only proposals; review wording, apply after semantic rewrite, then verify code-token preservation','rows':rows,'preserved':'All cite relation/comment strings, original historical source IDs such as E1.25/E1.55/E1.56 and BS-W8 provenance remain unchanged.'},ensure_ascii=False,indent=2));print('comment proposals',len(rows),'files',len({r['path'] for r in rows}))
