from pathlib import Path
import json,gzip,re,subprocess
W=Path('/tmp/bulk-w1-b3');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');mm=json.load(open(W/'module-map.json'));candidates={}
with gzip.open(W/'declaration-names.jsonl.gz','rt') as stream:
 for line in stream:
  row=json.loads(line);old=row['old'];new=row['new']
  if not row['private'] and old in mm and new is not None and mm[old]!=old and new!=mm[old]:candidates[old]={'old_name':old,'actual_name':new,'wrong_module_name':mm[old],'old_owner':row['old_module'],'new_owner':row['new_module']}
rows=[]
for path in sorted((R/'scripts').rglob('*.lean')):
 text=path.read_text();rel=str(path.relative_to(R));oldp=subprocess.run(['git','show','e381f75467755a84824a280ff429e52d4b6fb305:'+rel],cwd=R,capture_output=True,text=True);before=oldp.stdout if oldp.returncode==0 else ''
 for c in candidates.values():
  token='`'+c['wrong_module_name'];pat=re.compile(r'(?<![\w.`])'+re.escape(token)+r'(?![\w.])');matches=list(pat.finditer(text))
  if not matches:continue
  old_token='`'+c['old_name'];original_matches=list(re.finditer(r'(?<![\w.`])'+re.escape(old_token)+r'(?![\w.])',before));rows.append({'path':rel,**c,'current_single_quote_occurrences':len(matches),'frozen_original_single_quote_occurrences':len(original_matches),'lines':[text.count('\n',0,m.start())+1 for m in matches]})
summary={'candidate_constant_module_collisions':len(candidates),'rows':rows};(W/'module-name-quote-collisions.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2));print(json.dumps(summary,ensure_ascii=False,indent=2))
