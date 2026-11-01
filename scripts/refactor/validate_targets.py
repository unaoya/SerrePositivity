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
from lean_source import parse_source, read_source, add_import
from prune_imports import replace_imports
from split_module import ROOT, module_path, prepare, obtain_snapshot

FIELDS={'module','action','dest','moved','keep','attributes','candidate','note'}
OPTIONAL_FIELDS={'imports','downstream_imports'}
MODULE_NAME=re.compile(r"[\w']+(?:\.[\w']+)*")


def split_imports(entry):
    """Read exact replacement headers for split, move, or reimport."""
    if 'imports' not in entry:
        if entry['action']=='reimport': raise ValueError('reimport requires imports')
        return None
    if entry['action'] not in ('split','move','reimport'): raise ValueError('imports is only valid for split, move or reimport')
    value=entry['imports']
    expected={entry['module'],entry['dest']} if entry['action']=='split' else {entry['dest']}
    if not isinstance(value,dict) or set(value)!=expected:
        raise ValueError('imports must contain exactly '+('the source and destination modules' if entry['action']=='split' else 'the destination module'))
    for module, imports in value.items():
        if not isinstance(imports,list) or not all(isinstance(n,str) and MODULE_NAME.fullmatch(n) for n in imports):
            raise ValueError('imports must be arrays of module names')
        if len(imports)!=len(set(imports)): raise ValueError('duplicate import')
        if module in imports: raise ValueError('self import: '+module)
    return {n:set(ds) for n,ds in value.items()}



def downstream_imports(entry):
    value=entry.get('downstream_imports',{})
    if not isinstance(value,dict): raise ValueError('downstream_imports must be a module map')
    if 'downstream_imports' in entry and entry['action'] not in ('move','split','reimport'): raise ValueError('downstream_imports requires move, split or reimport')
    for module,deps in value.items():
        if not isinstance(module,str) or not MODULE_NAME.fullmatch(module): raise ValueError('invalid downstream module')
        if not isinstance(deps,list) or not all(isinstance(d,str) and MODULE_NAME.fullmatch(d) for d in deps):
            raise ValueError('downstream_imports must contain arrays of module names')
        if len(deps)!=len(set(deps)): raise ValueError('duplicate downstream import')
        if module in deps: raise ValueError('self downstream import: '+module)
    return {m:set(ds) for m,ds in value.items()}


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


def validate(root, entries, snapshots=None, config=None, *, return_graph=False):
    config=config or json.loads((ROOT/'scripts/refactor/layers.json').read_text())
    snapshots=snapshots or {}
    seen,destinations=set(),set()
    actions={}
    sources={}
    for entry in entries:
        if not isinstance(entry,dict) or not FIELDS<=set(entry) or set(entry)-(FIELDS|OPTIONAL_FIELDS):
            raise ValueError('expected required fields '+', '.join(sorted(FIELDS))+' and optional imports/downstream_imports')
        split_imports(entry)
        downstream_imports(entry)
        module, dest=entry['module'],entry['dest']
        src,dst=module_path(root,module),module_path(root,dest)
        # §10.30: only a split followed by a move of its keep side may share a source.
        previous=actions.get(module,[])
        if previous and not (previous==['split'] and entry['action']=='move'):
            raise ValueError('duplicate module: '+module)
        actions.setdefault(module,[]).append(entry['action'])
        if dest in destinations: raise ValueError('duplicate destination: '+dest)
        if entry['action']=='reimport':
            if module!=dest: raise ValueError('reimport requires dest equal to module')
        elif module==dest: raise ValueError('source equals destination')
        seen.add(module)
        if entry['action']!='reimport': destinations.add(dest)
        if not src.is_file(): raise ValueError('module does not exist: '+module)
        if entry['action']!='reimport' and dst.exists() and lc.code_only(read_source(dst)).strip() not in ('','module'):
            raise ValueError('destination is not an empty scaffold: '+dest)
        if entry['action'] not in ('move','split','archive','reimport'): raise ValueError('unknown action')
        for key in ('moved','keep'):
            if not isinstance(entry[key],list) or not all(isinstance(n,str) for n in entry[key]) or len(entry[key])!=len(set(entry[key])):
                raise ValueError('invalid declaration list: '+key)
        if not isinstance(entry['attributes'],dict) or not all(isinstance(k,str) and isinstance(v,list) and all(isinstance(a,str) for a in v) for k,v in entry['attributes'].items()):
            raise ValueError('attributes must map declaration names to lists of attributes')
        if not all(isinstance(entry[k],str) for k in ('candidate','note')): raise ValueError('candidate/note must be strings')
        if entry['action']=='split':
            source=parse_source(read_source(src),str(src),snapshot=snapshots.get(module),module=module);sources[module]=source
            names=set(source.declarations)
            moved,keep=set(entry['moved']),set(entry['keep'])
            if not moved or (moved|keep)-names: raise ValueError('unknown or empty moved/keep declaration list')
            if moved&keep: raise ValueError('moved and keep overlap')
            public={n for n,i in source.declarations.items() if source.commands[i].public}
            if public-(moved|keep): raise ValueError('uncovered public declarations: '+repr(sorted(public-(moved|keep))))
            if set(entry['attributes'])-names: raise ValueError('attributes name an unknown declaration')
        elif entry['moved'] or entry['keep']:
            raise ValueError('move/archive/reimport require empty moved and keep lists')
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
        for mod in (plan['module'],plan['dest']):
            text=plan['changes'][mod]['after']
            changed_sources[mod]=text;after[mod]=lc.imports(text)
    # Apply exact headers, then only explicit downstream_imports (§10.14).
    # Evidence is reviewed by the coordinator; this field does not itself prove
    # compilation or preservation. It must be copied from the restored split trial.
    for entry in entries:
        overrides=split_imports(entry)
        if overrides is None: continue
        for mod,deps in overrides.items():
            if entry['action']=='move':
                if entry['module'] in deps: raise ValueError('self import through pre-move name: '+entry['module'])
                mod=entry['module']
            missing={d for d in deps if lc.under(d,'SerrePositivity') and d not in after}
            if missing: raise ValueError('imports refer to missing project modules: '+repr(sorted(missing)))
            text=changed_sources.get(mod)
            if text is None: text=read_source(module_path(root,mod))
            if lc.imports(text): text=replace_imports(text,deps)
            else:
                for dep in sorted(deps): text=add_import(text,dep)
            changed_sources[mod]=text
            after[mod]=deps
    downstream_additions={}
    for entry in entries:
        for mod,deps in downstream_imports(entry).items():
            if mod not in after: raise ValueError('missing downstream module: '+mod)
            missing={d for d in deps if lc.under(d,'SerrePositivity') and d not in after}
            if missing: raise ValueError('downstream_imports refer to missing project modules: '+repr(sorted(missing)))
            downstream_additions.setdefault(mod,set()).update(deps)
            after[mod] |= deps
            text=changed_sources.get(mod)
            if text is None: text=read_source(module_path(root,mod))
            for dep in sorted(deps): text=add_import(text,dep)
            changed_sources[mod]=text
    if split_plans:
        nodes,index,masks=lc.closure_masks(after)
        for plan in split_plans:
            module,dest=plan['module'],plan['dest']
            forward=bool(masks[dest] & (1<<index[module]))
            backward=bool(masks[module] & (1<<index[dest]))
            if forward and backward: raise ValueError('split imports create an import cycle: '+module)
            if plan['dependencies']['moved_to_keep'] and not forward:
                raise ValueError('split imports lose moved-to-keep dependency: '+module)
            if plan['dependencies']['keep_to_moved'] and not backward:
                raise ValueError('split imports lose keep-to-moved dependency: '+module)
    # Splits and their headers/dependencies are already composed above; moves
    # rename the resulting keep nodes and all incoming edges, never the original body.
    renames={e['module']:e['dest'] for e in entries if e['action'] in ('move','archive')}
    after={renames.get(n,n):{renames.get(d,d) for d in deps} for n,deps in after.items()}
    if any('imports' in e or e.get('downstream_imports') for e in entries):
        nodes,index,masks=lc.closure_masks(after)
        changed={renames.get(e['module'],e['module']) for e in entries if 'imports' in e}
        changed |= {e['dest'] for e in entries if e['action']=='split' and 'imports' in e}
        changed |= {renames.get(m,m) for m in downstream_additions}
        for module in sorted(changed):
            if any(masks[d] & (1<<index[module]) for d in after[module]):
                raise ValueError('imports create an import cycle: '+module)
    from importlib.util import spec_from_file_location, module_from_spec
    spec=spec_from_file_location('target_moves',ROOT/'scripts/move_module.py')
    moves_tool=module_from_spec(spec);spec.loader.exec_module(moves_tool)
    for mod in graph.keys() | changed_sources.keys():
        if not lc.under(renames.get(mod,mod),config['model_category_rule']['prefix']): continue
        if mod in changed_sources or graph[mod] & renames.keys():
            text=changed_sources.get(mod)
            if text is None: text=read_source(module_path(root,mod))
            changed_sources[mod]=moves_tool.rewrite(text,renames,{})
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
    result={'status':'FAIL' if increases else 'PASS','target_count':len(entries),
            'layer_increases':increases,
            'before':{'direct_by_pair':before_report['direct_by_pair'],
                      'closure':{t:before_report['tiers'][t]['forbidden_module_count'] for t in lc.TIERS},
                      'entry_edges':{t:before_report['tiers'][t]['entry_edges'] for t in lc.TIERS}},
            'after':{'direct_by_pair':after_report['direct_by_pair'],
                     'closure':{t:after_report['tiers'][t]['forbidden_module_count'] for t in lc.TIERS},
                     'entry_edges':{t:after_report['tiers'][t]['entry_edges'] for t in lc.TIERS}},
            'split_directions':[{'module':p['module'],**p['dependencies']} for p in split_plans],
            'consumer_import_additions':{},
            'downstream_imports':{renames.get(m,m):sorted(renames.get(d,d) for d in ds) for m,ds in sorted(downstream_additions.items())}}
    if return_graph: return result,graph,after,mentions,after_mentions
    return result


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
