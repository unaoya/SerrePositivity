from pathlib import Path
import json,contextlib
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');prefix=(W/'apply_bundle_docs.py').read_text().split("for mod in manifest['files']:")[0];e={}
with contextlib.redirect_stdout(open(W/'doc-module-discovery.log','w')):exec(prefix,e)
manifest=json.loads((W/'final-bundle/manifest.json').read_text());moves=e['modulemap'];extra=set(json.loads((W/'additional-doc-modules.json').read_text()));rows=[]
for p in (R/'SerrePositivity/BhattScholze').rglob('*.lean'):
 rel=p.relative_to(R).as_posix();m=rel[:-5].replace('/','.');dest=moves.get(m,m)
 if dest in manifest['files']:continue
 t=p.read_text();changed=[]
 for a,b in e['comments'](t):
  old=t[a:b];new=e['update'](old,rel);new=e['pattern'].sub(lambda m:e['names'][m[0]],new);new=e['path_pattern'].sub(lambda m:e['path_names'][m[0]],new)
  if new!=old:changed.append({'line':t.count('\n',0,a)+1,'before':old,'after':new})
 if changed:extra.add(m);rows.append({'module':m,'comment_changes':changed})
(W/'additional-doc-modules.json').write_text(json.dumps(sorted(extra),ensure_ascii=False,indent=2));(W/'additional-path-doc-discovery.json').write_text(json.dumps({'status':'comment-only preview scope; native capture/build/v3b still required for new modules','additional_modules':len(rows),'rows':rows},ensure_ascii=False,indent=2));print('additional path-only prose modules',len(rows),'total comment-only extras',len(extra));print([r['module'] for r in rows])
