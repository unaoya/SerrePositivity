#!/usr/bin/env python3
"""概要：移動・分割・archive の確定リストを実施前に検査する。
方針：宣言抽出を分割道具と共有し、変更後の import グラフを模擬する。
規約：実ファイルは変えない。使われ方：targets.json... [--snapshot MODULE=FILE]。
"""
import argparse
import json
from pathlib import Path
import re
import sys

import layer_check as lc
from lean_source import parse_source, read_source
from split_module import ROOT, module_path, prepare, obtain_snapshot

FIELDS={'module','action','dest','moved','keep','attributes','candidate','note'}


def simulated_model_mentions(root, mentions, renames, changed_sources, config):
    rule=config['model_category_rule']
    result=set(mentions)-renames.keys()-changed_sources.keys()
    for old in set(renames)|set(changed_sources):
        new=renames.get(old,old)
        if not lc.under(new,rule['prefix']): continue
        text=changed_sources.get(old)
        if text is None: text=read_source(module_path(root,old))
        if rule['code_contains'] in lc.code_only(text): result.add(new)
    return result


def validate(root, entries, snapshots=None, config=None):
    config=config or json.loads((ROOT/'scripts/refactor/layers.json').read_text())
    snapshots=snapshots or {}
    seen,destinations=set(),set()
    sources={}
    for entry in entries:
        if not isinstance(entry,dict) or set(entry)!=FIELDS: raise ValueError('expected exactly fields: '+', '.join(sorted(FIELDS)))
        module, dest=entry['module'],entry['dest']
        src,dst=module_path(root,module),module_path(root,dest)
        if module in seen: raise ValueError('duplicate module: '+module)
        if dest in destinations: raise ValueError('duplicate destination: '+dest)
        if module==dest: raise ValueError('source equals destination')
        seen.add(module);destinations.add(dest)
        if not src.is_file(): raise ValueError('module does not exist: '+module)
        if dst.exists() and lc.code_only(read_source(dst)).strip() not in ('','module'):
            raise ValueError('destination is not an empty scaffold: '+dest)
        if entry['action'] not in ('move','split','archive'): raise ValueError('unknown action')
        for key in ('moved','keep'):
            if not isinstance(entry[key],list) or not all(isinstance(n,str) for n in entry[key]) or len(entry[key])!=len(set(entry[key])):
                raise ValueError('invalid declaration list: '+key)
        if not isinstance(entry['attributes'],dict) or not all(isinstance(k,str) and isinstance(v,list) and all(isinstance(a,str) for a in v) for k,v in entry['attributes'].items()):
            raise ValueError('attributes must map declaration names to lists of attributes')
        if not all(isinstance(entry[k],str) for k in ('candidate','note')): raise ValueError('candidate/note must be strings')
        if entry['action']=='split':
            source=parse_source(read_source(src),str(src));sources[module]=source
            names=set(source.declarations)
            moved,keep=set(entry['moved']),set(entry['keep'])
            if not moved or (moved|keep)-names: raise ValueError('unknown or empty moved/keep declaration list')
            if moved&keep: raise ValueError('moved and keep overlap')
            public={n for n,i in source.declarations.items() if source.commands[i].public}
            if public-(moved|keep): raise ValueError('uncovered public declarations: '+repr(sorted(public-(moved|keep))))
            if set(entry['attributes'])-names: raise ValueError('attributes name an unknown declaration')
        elif entry['moved'] or entry['keep']:
            raise ValueError('move/archive require empty moved and keep lists')
    if seen&destinations: raise ValueError('destination is also a source; chained moves require a separate window')
    graph,mentions=lc.read_graph(root,config)
    for entry in entries:
        if entry['action']=='archive':
            outside=sorted(n for n,deps in graph.items() if entry['module'] in deps and n not in seen)
            if outside: raise ValueError('archive still has outside importers: '+repr(outside))
    after={n:set(ds) for n,ds in graph.items()}
    changed_sources={}
    split_plans=[]
    for entry in entries:
        if entry['action']!='split': continue
        module=entry['module']
        snap=snapshots.get(module)
        if snap is None: snap=obtain_snapshot(root,module)
        plan=prepare(root,module,entry['dest'],entry['moved'],snap,graph)
        split_plans.append(plan)
        for mod,change in plan['changes'].items():
            if mod in changed_sources and change['after']!=changed_sources[mod]:
                # Consumer import additions can be composed; overlapping source rewrites cannot.
                if mod in seen or mod in destinations: raise ValueError('overlapping split edits: '+mod)
                after[mod] |= lc.imports(change['after'])
            else:
                changed_sources[mod]=change['after'];after[mod]=lc.imports(change['after'])
    renames={e['module']:e['dest'] for e in entries if e['action'] in ('move','archive')}
    after={renames.get(n,n):{renames.get(d,d) for d in deps} for n,deps in after.items()}
    after_mentions=simulated_model_mentions(root,mentions,renames,changed_sources,config)
    before_report=lc.analyze(graph,mentions,config)
    after_report=lc.analyze(after,after_mentions,config)
    # Compare a moved root with its former identity; a rename alone is not an increase.
    baseline={**before_report,'ratchet_metrics':dict(before_report['ratchet_metrics'])}
    for old,new in renames.items():
        for tier in lc.TIERS:
            key=f'closure/{tier}/{old}'
            if key in baseline['ratchet_metrics']:
                baseline['ratchet_metrics'][f'closure/{tier}/{new}']=baseline['ratchet_metrics'].pop(key)
    increases=lc.ratchet_increases(after_report,baseline)
    return {'status':'FAIL' if increases else 'PASS','target_count':len(entries),
            'layer_increases':increases,
            'before':{'direct_by_pair':before_report['direct_by_pair'],
                      'closure':{t:before_report['tiers'][t]['forbidden_module_count'] for t in lc.TIERS}},
            'after':{'direct_by_pair':after_report['direct_by_pair'],
                     'closure':{t:after_report['tiers'][t]['forbidden_module_count'] for t in lc.TIERS}},
            'split_directions':[{'module':p['module'],**p['dependencies']} for p in split_plans]}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('plans',type=Path,nargs='+');parser.add_argument('--root',type=Path,default=ROOT)
    parser.add_argument('--snapshot',action='append',default=[],metavar='MODULE=FILE')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    try:
        entries=[]
        for p in args.plans:
            data=json.loads(p.read_text())
            if not isinstance(data,list): raise ValueError('target JSON must be an array')
            entries.extend(data)
        if not entries: raise ValueError('empty target list')
        snapshots={}
        for value in args.snapshot:
            module,path=value.split('=',1)
            snapshots[module]=json.loads(Path(path).read_text())
        result=validate(args.root.resolve(),entries,snapshots)
        text=json.dumps(result,ensure_ascii=False,indent=2)+'\n';print(text,end='')
        if args.output: args.output.write_text(text)
        return int(result['status']=='FAIL')
    except (OSError,ValueError,KeyError,TypeError) as exc:
        print('validate_targets: FAIL: '+str(exc),file=sys.stderr);return 1


if __name__=='__main__':sys.exit(main())
