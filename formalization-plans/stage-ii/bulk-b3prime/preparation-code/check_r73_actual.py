from pathlib import Path
import json,sys
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');sys.path.insert(0,str(R/'scripts/refactor'));from layer_check import imports
old=json.loads((W/'r7-3b-edge-ledger.json').read_text());mp=json.loads((W/'B4/module-map.json').read_text());rows=[]
for row in old['rows']:
 m=mp.get(row['original_importer'],row['original_importer']);actual=imports((R/(m.replace('.','/')+'.lean')).read_text());retained=row['decision'].startswith('retained:');already=row['decision'].startswith('already resolved');old_present=row['original_import'] in actual;targets=row['target_owners'];missing=sorted(set(targets)-actual)
 assert not missing,(m,missing)
 if retained:assert old_present,m
 else:assert not old_present,m
 rows.append({**row,'actual_importer':m,'actual_project_imports':sorted(d for d in actual if d.startswith('SerrePositivity')),'original_direct_edge_present':old_present,'all_target_owners_directly_imported':not missing,'final_disposition':'retained' if retained else 'already-baseline' if already else 'resolved-in-B3prime'})
result={'status':'actual source, all target builds and full native v3b passed; final formal audits in progress','review_edges':8,'already_baseline':sum(r['final_disposition']=='already-baseline' for r in rows),'resolved_in_B3prime':sum(r['final_disposition']=='resolved-in-B3prime' for r in rows),'retained':sum(r['final_disposition']=='retained' for r in rows),'rows':rows};assert (result['already_baseline'],result['resolved_in_B3prime'],result['retained'])==(2,5,1);(W/'r7-3b-actual-edge-ledger.json').write_text(json.dumps(result,ensure_ascii=False,indent=2));print('R7-3b actual8: baseline2, resolved5, retained1')
