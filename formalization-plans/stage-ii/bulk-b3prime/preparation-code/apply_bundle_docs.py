from pathlib import Path
import json,re,sys,hashlib
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');D=R/'formalization-plans/stage-ii/bulk-b3prime';B=W/'final-bundle';sys.path.insert(0,str(W));sys.path.insert(0,str(R/'scripts/refactor'));from doc_changes import comments,update;from layer_check import code_only
manifest=json.loads((B/'manifest.json').read_text());modulemap=json.loads((W/'namespace-rewrite-plan.json').read_text())['modules'];names={r['old']:r['new'] for r in json.loads((D/'namespace-map.proposed.json').read_text())['rows'] if r['old']!=r['new']};pattern=re.compile('|'.join(re.escape(n)+r"(?![\w'])" for n in sorted(names,key=len,reverse=True)));records=[]
for mod in manifest['files']:
 p=B/(mod.replace('.','/')+'.lean');original=p.read_text();assert hashlib.sha256(original.encode()).hexdigest()==manifest['files'][mod];text=original;count=0
 for a,b in reversed(list(comments(original))):
  before=original[a:b];after=update(before,p.relative_to(B).as_posix());after=pattern.sub(lambda m:names[m[0]],after)
  for old,new in modulemap.items():after=after.replace(old,new).replace(old.replace('.','/'),new.replace('.','/'))
  if mod=='SerrePositivity.BhattScholze.Perfectoidization.CompletedTensor' and before.startswith('/-!') and '# perfectoid 環の完備テンソル積' in before:
   after=after.replace('## 方針','§10 の共通部分：PerfectoidCompletedTensorDiscrete 節は、Lemma 10.3 で使う\n元の完備導来テンソル積の離散性と、その H⁰ の perfectoid 性を扱う。\n§8 のテンソルの普遍性と §10 の almost 比較が共有するため、このファイルに置く。\n\n## 方針',1)
  if before!=after:text=text[:a]+after+text[b:];count+=1
 def noncomments(source):
  result=[];at=0
  for lo,hi in comments(source):result.append(source[at:lo]);at=hi
  result.append(source[at:]);return ''.join(result)
 assert noncomments(text)==noncomments(original),'comment rewrite touched Lean tokens or strings: '+mod
 # The comment lexer cannot alter any noncomment span, including citation relation/comment strings.
 if count:
  p.write_text(text);manifest['files'][mod]=hashlib.sha256(text.encode()).hexdigest();records.append({'module':mod,'comments_changed':count,'before_sha256':hashlib.sha256(original.encode()).hexdigest(),'after_sha256':manifest['files'][mod]})
manifest['comment_edits']=records;(B/'manifest.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n');(W/'bundle-docs-receipt.json').write_text(json.dumps({'status':'comment-only source transformations; no attribute-string changes; full validation pending','files':records,'comments_changed':sum(r['comments_changed'] for r in records)},ensure_ascii=False,indent=2));print('doc files',len(records),'comments',sum(r['comments_changed'] for r in records))
