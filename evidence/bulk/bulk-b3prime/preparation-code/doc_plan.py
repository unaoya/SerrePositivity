from pathlib import Path
import re,json,collections
R=Path.cwd();D=R/'evidence/bulk/bulk-b3prime'
def comments(s):
 i=0
 while i<len(s):
  if s[i]=='"':
   i+=1
   while i<len(s):
    if s[i]=='\\':i+=2
    elif s[i]=='"':i+=1;break
    else:i+=1
  elif s.startswith('--',i):
   end=s.find('\n',i);end=len(s) if end<0 else end;yield i,end;slice_=s[i:end];i=end
  elif s.startswith('/-',i):
   start=i;i+=2;depth=1
   while i<len(s) and depth:
    if s.startswith('/-',i):depth+=1;i+=2
    elif s.startswith('-/',i):depth-=1;i+=2
    else:i+=1
   assert depth==0;yield start,i
  else:i+=1
rx=re.compile(r'(?<![\w])(?:[DEG][0-9]+[a-z]?(?:-[0-9]+)?|W[0-9]+|Π[0-9]+(?:-[0-9]+)?)(?![\w])');rows=[];counts=collections.Counter()
for root in ['Semiperfectoid','Andre','Perfectoidization','Almost','PerfectoidIdeal','IntegralPerfectoidization']:
 for p in (R/'SerrePositivity/BhattScholze'/root).rglob('*.lean'):
  s=p.read_text()
  for a,b in comments(s):
   for m in rx.finditer(s[a:b]):
    pos=a+m.start();line=s.count('\n',0,pos)+1;counts[m[0]]+=1;rows.append({'path':p.relative_to(R).as_posix(),'line':line,'token':m[0],'comment_start':a,'comment_stop':b,'line_text':s[s.rfind('\n',0,pos)+1:s.find('\n',pos) if s.find('\n',pos)>=0 else len(s)]})
Path('/tmp/bulk-b3prime/doc-comment-labels.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2));print('comment labels',len(rows));print(counts)
for token in counts:
 print(token, ' | '.join(r['line_text'][:120] for r in rows if r['token']==token)[:300])
