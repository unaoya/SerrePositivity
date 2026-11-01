#!/usr/bin/env python3
"""概要：IF-W0-3 W1 候補の import 閉包を再現可能に計測する。
方針：明示した候補だけを、同時移動を仮定した最大の閉じた集合へ絞る。
規約：Lean は変更しない。split は自動推測せず保留。Mathlib 等の外部は終端。
使われ方：python3 -B scripts/refactor/targets_builder.py --output-dir .lake/verify/ifw0-3
この道具の採用判定は宣言の数学的分類の代用ではない。JSON の確定には読解と
validate_targets.py の検査を併用する。現在は W1 のみを実装する。
"""
from __future__ import annotations
import argparse
from collections import Counter, deque
import json
import re
from pathlib import Path
import time
import layer_check as lc

ROOT = Path(__file__).resolve().parents[2]
IC = lc.IC


def candidates(graph, config):
    result = {}
    def add(module, dest, candidate, group):
        if module in result:
            row = result[module]
            if row['dest'] != dest:
                raise ValueError('conflicting proposed destination: ' + module)
            row['candidates'] = sorted(set(row['candidates'] + [candidate]))
            return
        if module not in graph:
            raise ValueError('missing candidate: ' + module)
        result[module] = dict(module=module, dest=dest, candidates=[candidate], group=group)
    for name in 'StableCategories ExactEnrichment StableInfinity VerdierSequence VerdierDiagrams AdjointVerdier AdjointLocalization'.split():
        layer = ('F1B.Localization' if name == 'AdjointLocalization' else
                 'Stable.Infinity' if name in ('ExactEnrichment', 'StableInfinity', 'VerdierDiagrams') else 'Stable.Verdier')
        add('SerrePositivity.KST.LocalizingInvariants.' + name, IC+'.'+layer+'.'+name, 'R48', 'LI 基礎ブロック7本（Verdier §1.2）')
    for name in 'ExactFunctorCategory ExactFunctorCategoryEquivalence StableVerdierSequence'.split():
        layer = 'Stable.Verdier' if name == 'StableVerdierSequence' else 'Stable.Exact'
        add(IC+'.Derived.'+name, IC+'.'+layer+'.'+name, 'R49a', 'Derived 完全関手・Verdier（Verdier §1.2）')
    for name in 'ExactFunctorDescent RestrictedDeformationLocalization CofiberBottomIsoTransport FullSubcomplexHomotopyLift HomotopyPrecompVertex RestrictedDeformationHomotopy'.split():
        layer = 'Stable.Exact' if name in ('ExactFunctorDescent','CofiberBottomIsoTransport') else 'F1B.Localization' if name == 'RestrictedDeformationLocalization' else 'F1B'
        add(IC+'.Derived.'+name, IC+'.'+layer+'.'+name, 'R49b', 'Derived 一般部分（指示書 §4.1）')
    pairs = [('F1','F2',28,'R26'), ('Stable','Derived',10,'R39'), ('F2','Derived',7,'R39'), ('F1','Derived',4,'R71'), ('HomotopyLimits','Derived',3,'R71')]
    counts = []
    for a,b,expected,candidate in pairs:
        edges = sorted((n,d) for n,deps in graph.items() if lc.classify(n,config)==a
                       for d in deps if lc.classify(d,config)==b)
        counts.append(dict(source=a, target=b, expected=expected, edges=len(edges), targets=len({d for _,d in edges})))
        if len(edges) != expected:
            raise ValueError(f'instruction count mismatch: {a} -> {b}: expected {expected}, got {len(edges)}')
        for module in sorted({d for _,d in edges}):
            if module == IC+'.Derived.CoherentBar.Compact.All':
                continue  # R39: aggregate edit, explicitly outside JSON.
            name = module.rsplit('.',1)[1]
            if module in result:
                add(module,result[module]['dest'],candidate,result[module]['group'])
                continue
            if candidate=='R26':
                layer = 'Core' if name in ('FunctorIsoWhiskerHom', 'FunctorIsoWhiskerAlgebra', 'FunctorIsoWhiskerComposition', 'FunctorIsoTransport') else 'F1B'
            else:
                layer = 'Core' if name in ('ConeEdgeCompatibility','RightFibrationReflection') else 'F1B'
            add(module, IC+'.'+layer+'.'+name, candidate, 'R2-A §4/§5・計画 §4 の入口参照先')
    for name in ('SpecifiedHomotopyLift','SpecifiedFunctorEdgeLift'):
        add(IC+'.F2.CatInfinity.'+name, IC+'.F1B.'+name, 'R26', 'R49b 前提の追加2本（指示書 §4.1）')
    for suffix in ('DoldKanComparison.UniverseHomotopy','DoldKanComparison.UniverseKan','DGNerve.JoinSimplexInclusions','DGNerve.JoinSimplexFaces','DGNerve.JoinVertexSurjectivity'):
        add(IC+'.'+suffix,IC+('.Simplicial.' if suffix.endswith('.UniverseKan') else '.Core.')+suffix.rsplit('.',1)[1], 'R66', '単体的集合の一般補題（計画 §5 段C）')
    for name,layer in [('EnrichedFunctorCollageNerve','F1B'), ('ContractibleKanProducts','Core')]:
        add('SerrePositivity.KST.SConstruction.'+name,IC+'.'+layer+'.'+name,'R71','SC-C1/SC-C3（外部調査 §2）')
    add(IC+'.F2.Idempotent.Retracts',IC+'.Core.Retracts','R53','retract 閉包（指示書 §4.1）')
    return result, counts


def disallowed(destination, dependency, config):
    layer = lc.classify(destination, config)
    if layer is None:
        return True
    if lc.forbidden(dependency,'W1',config,set()):
        return True
    if lc.direct_reasons(destination,dependency,config):
        return True
    # A repository module outside the specified layer tree has not been certified
    # as an allowed dependency. Never infer permission from absence of a ban.
    return lc.under(dependency,'SerrePositivity') and lc.classify(dependency,config) is None


def closed_moves(graph, proposals, config, collisions=()):
    nodes,index,masks = lc.closure_masks(graph)
    closures = {m:lc.selected_names(masks[m] & ~(1<<index[m]),nodes) for m in proposals}
    accepted = set(proposals)-set(collisions)
    while True:
        renamed = {m:proposals[m]['dest'] for m in accepted}
        remove = {m for m in accepted if any(disallowed(proposals[m]['dest'],renamed.get(d,d),config)
                                            for d in closures[m])}
        if not remove:
            break
        accepted -= remove
    renamed = {m:proposals[m]['dest'] for m in accepted}
    evidence = {}
    for m,p in sorted(proposals.items()):
        deps = closures[m]
        bad = [d for d in deps if disallowed(p['dest'],renamed.get(d,d),config)]
        evidence[m] = {**p, 'accepted':m in accepted, 'collision':m in collisions,
                       'closure_count':len(deps),
                       'repository_closure_count':sum(lc.under(d,'SerrePositivity') for d in deps),
                       'groups_before':dict(sorted(Counter(lc.group(d,config) for d in deps if lc.under(d,'SerrePositivity')).items())),
                       'groups_after':dict(sorted(Counter(lc.group(renamed.get(d,d),config) for d in deps if lc.under(d,'SerrePositivity')).items())),
                       'blocked_dependencies':bad, 'witness':witness(graph,m,set(bad))}
    return accepted, evidence


def witness(graph, root, blocked):
    queue=deque([root]); paths={root:[root]}
    while queue:
        node=queue.popleft()
        if node in blocked:
            return paths[node]
        for dep in sorted(graph.get(node,())):
            if dep not in paths:
                paths[dep]=paths[node]+[dep];queue.append(dep)
    return []


def renamed_graph(graph, renames):
    return {renames.get(n,n):{renames.get(d,d) for d in deps} for n,deps in graph.items()}



def edit_edges(graph, removals=(), additions=(), renames=None):
    """手作業の指定を厳密に適用する。存在しない削除辺は誤記として拒否。"""
    after={n:set(ds) for n,ds in graph.items()}; renames=renames or {}
    def edge(item):
        if not isinstance(item,dict) or set(item)!={'from','to'}:
            raise ValueError('edge must have exactly from and to')
        if not all(isinstance(v,str) for v in item.values()):raise ValueError('edge names must be strings')
        return tuple(renames.get(item[k],item[k]) for k in ('from','to'))
    seen=set()
    for item in removals:
        src,dst=edge(item)
        if (src,dst) in seen:raise ValueError('duplicate removed edge')
        seen.add((src,dst))
        if dst not in after.get(src,set()):raise ValueError('removed edge does not exist: '+src+' -> '+dst)
        after[src].remove(dst)
    for item in additions:
        src,dst=edge(item)
        if src not in after:raise ValueError('added edge source does not exist: '+src)
        if lc.under(dst,'SerrePositivity') and dst not in after:raise ValueError('added edge target does not exist: '+dst)
        after[src].add(dst)
    return after


def manual_modules(graph, spec, renames=None):
    """R61/R63: redirect duplicate modules and replace evidence-specified headers."""
    renames=renames or {}
    if set(spec)-{'redirects','imports'}:raise ValueError('unknown manual module field')
    redirects={renames.get(k,k):renames.get(v,v) for k,v in spec.get('redirects',{}).items()}
    if redirects.keys() & set(redirects.values()):raise ValueError('chained manual redirects')
    if any(k==v or k not in graph or v not in graph for k,v in redirects.items()):
        raise ValueError('manual redirect requires distinct existing modules')
    after={n:set(ds) for n,ds in graph.items()}
    for key,deps in spec.get('imports',{}).items():
        key=renames.get(key,key)
        if key not in after or not isinstance(deps,list) or len(deps)!=len(set(deps)):
            raise ValueError('invalid manual import override')
        deps={renames.get(d,d) for d in deps}
        if any(lc.under(d,'SerrePositivity') and d not in after for d in deps):
            raise ValueError('missing manual dependency')
        after[key]=deps
    after={n:{redirects.get(d,d) for d in ds} for n,ds in after.items() if n not in redirects}
    if any(n in ds for n,ds in after.items()):raise ValueError('manual redirect creates self import')
    return after


def pull_down(graph, module, destination, config, mentions, renames=None):
    """v自身を含む S(v)。閉包のDG/KST/モデル圏も別に返す。"""
    renames=renames or {};nodes,index,masks=lc.closure_masks(graph)
    deps=lc.selected_names(masks[module],nodes)
    rank={l['name']:l['rank'] for l in config['layers']}
    target=lc.classify(destination,config)
    if target not in rank:raise ValueError('unknown destination layer')
    members=[n for n in deps if n==module or
             (lc.classify(renames.get(n,n),config) in rank and rank[lc.classify(renames.get(n,n),config)]>rank[target])]
    model_prefixes=[p for p in config['forbidden']['W2a_additions'] if '.HomotopicalAlgebra.' in p or p.endswith('.ModelBridge')]
    blocked=[n for n in deps if lc.under(n,'SerrePositivity.DifferentialGraded') or lc.under(n,'SerrePositivity.KST') or
             n in mentions or any(lc.under(n,p) for p in model_prefixes)]
    return {'members':members,'count':len(members),'polluted':blocked,'within_limit':len(members)<=60}


def transitive_users(graph, module):
    reverse={n:set() for n in graph}
    for n,deps in graph.items():
        for d in deps:reverse.setdefault(d,set()).add(n)
    found=set();pending=list(reverse.get(module,()))
    while pending:
        n=pending.pop()
        if n in found or n==module:continue
        found.add(n);pending.extend(reverse.get(n,()))
    return sorted(found)


def w1_condition(report, baseline=None):
    names=report['tiers']['W1']['forbidden_modules']
    counts={p:sum(lc.under(n,'SerrePositivity.'+p) for n in names)
            for p in ('DifferentialGraded','EInfinity')}
    direct=sum(report['direct_by_pair'].values())
    before=sum((baseline or report)['direct_by_pair'].values())
    return {'passes':not any(counts.values()) and direct<=before,'counts':counts,
            'direct_violations':direct,'baseline_direct_violations':before,'direct_not_increased':direct<=before}


def simulate_plans(args):
    # Reuse the validator's exact split preparation, overrides and cumulative
    # rename rules; never emulate a pruned split by dropping arbitrary edges.
    from validate_targets import validate
    config=json.loads((args.root/'scripts/refactor/layers.json').read_text())
    snapshots={m:json.loads(Path(p).read_text()) for m,p in (v.split('=',1) for v in args.snapshot)}
    def rows(paths):
        result=[]
        for path in paths:
            data=json.loads(path.read_text())
            if not isinstance(data,list):raise ValueError('plan must be an array')
            result.extend(data)
        return result
    current=rows(args.plans);future=rows(args.future_plans)
    result,before,after,mentions,after_mentions=validate(args.root,current,snapshots,config,return_graph=True)
    renames={e['module']:e['dest'] for e in current if e['action'] in ('move','archive')}
    removals=json.loads(args.remove_edges.read_text()) if args.remove_edges else []
    additions=json.loads(args.add_edges.read_text()) if args.add_edges else []
    spec_path=getattr(args,'manual_modules',None)
    spec=json.loads(spec_path.read_text()) if spec_path else {}
    manual=manual_modules(edit_edges(after,removals,additions,renames),spec,renames)
    reports={'before':lc.analyze(before,mentions,config), 'targets':lc.analyze(after,after_mentions,config),
             'manual':lc.analyze(manual,after_mentions,config)}
    if future:
        _,_,later,_,later_mentions=validate(args.root,current+future,snapshots,config,return_graph=True)
        aliases={e['module']:e['dest'] for e in current+future if e['action'] in ('move','archive')}
        later=manual_modules(edit_edges(later,removals,additions,aliases),spec,aliases)
        reports['conditional_future']=lc.analyze(later,later_mentions,config)
    args.output_dir.mkdir(parents=True,exist_ok=True)
    for name,report in reports.items():
        (args.output_dir/(name+'.json')).write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    summary={'validator_status':result['status'],'current_plans':[str(p) for p in args.plans],
             'future_plans':[str(p) for p in args.future_plans], 'removed_edges':removals,'added_edges':additions,'manual_modules':spec,
             'conditions':{name:w1_condition(r,reports['before']) for name,r in reports.items()}}
    (args.output_dir/'simulation.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(summary,ensure_ascii=False,indent=2))


def roof_cluster(graph, sources):
    """§10.6: Derived-only reachability and identifier-boundary DG vocabulary."""
    seeds=[IC+'.Derived.'+n for n in ('SliceEvaluationPinched','RightFibrationTerminalRepresentation','RoofTargetFunctor')]
    found=set();todo=list(seeds)
    while todo:
        m=todo.pop()
        if m in found: continue
        found.add(m);todo.extend(d for d in graph.get(m,()) if lc.under(d,IC+'.Derived'))
    terms=['DG*','dg*','Cochain','HomologicalComplex','ChainComplex','ModuleCat','CommRing','Bimodule']
    identifiers=re.compile(r"[^\W\d][\w']*",re.UNICODE)
    exact=set(terms[2:])
    excluded={}
    for m in sorted(found):
        code=lc.code_only(sources(m))
        hits={}
        for i,line in enumerate(code.splitlines(),1):
            for token in set(identifiers.findall(line)):
                if token.startswith(('DG','dg')) or token in exact:
                    hits.setdefault(token,[]).append({'line':i,'text':line.strip()})
        if hits: excluded[m]=hits
    cluster=found-excluded.keys()
    prefixes=[IC+'.Derived',IC+'.DGNerve',IC+'.DoldKanComparison','SerrePositivity.DifferentialGraded','SerrePositivity.KST']
    leaks=[{'from':m,'to':d} for m in sorted(cluster) for d in sorted(graph.get(m,()))
           if d not in cluster and any(lc.under(d,p) for p in prefixes)]
    return {'seeds':seeds,'vocabulary':terms,'matching':'case-sensitive identifier boundaries on code_only (including imports); DG/dg prefixes, other terms exact',
            'derived_closure':sorted(found),'cluster':sorted(cluster),'excluded':excluded,'leaks':leaks}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=ROOT)
    parser.add_argument('--roof',action='store_true')
    parser.add_argument('--output-dir',type=Path,required=True)
    parser.add_argument('--plans',type=Path,nargs='+')
    parser.add_argument('--future-plans',type=Path,nargs='*',default=[])
    parser.add_argument('--remove-edges',type=Path)
    parser.add_argument('--add-edges',type=Path)
    parser.add_argument('--manual-modules',type=Path)
    parser.add_argument('--snapshot',action='append',default=[],metavar='MODULE=FILE')
    args=parser.parse_args(); start=time.monotonic()
    if args.plans:
        simulate_plans(args);return
    if args.future_plans or args.remove_edges or args.add_edges or args.manual_modules or args.snapshot:
        parser.error('simulation options require --plans')
    config=json.loads((args.root/'scripts/refactor/layers.json').read_text())
    graph,mentions=lc.read_graph(args.root,config)
    if args.roof:
        result=roof_cluster(graph,lambda m:(args.root/(m.replace('.','/')+'.lean')).read_text())
        args.output_dir.mkdir(parents=True,exist_ok=True)
        (args.output_dir/'roof-cluster.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
        print(json.dumps({k:len(result[k]) for k in ('derived_closure','cluster','excluded','leaks')}));return
    proposals,counts=candidates(graph,config)
    destinations=Counter(p['dest'] for p in proposals.values())
    collisions={m for m,p in proposals.items() if destinations[p['dest']]>1 or p['dest'] in proposals or
                (p['dest'] in graph and lc.code_only((args.root/(p['dest'].replace('.','/')+'.lean')).read_text()).strip() not in ('','module'))}
    accepted,evidence=closed_moves(graph,proposals,config,collisions)
    rows=[]
    for m in sorted(accepted):
        e=evidence[m]
        rows.append(dict(module=m,action='move',dest=e['dest'],moved=[],keep=[],attributes={},
                         candidate='/'.join(e['candidates']),
                         note=f"§3.2-2 move：同時移動後の閉包は許可層内。依存 {e['closure_count']}（repo {e['repository_closure_count']}、自己除外、外部は終端）。{e['group']}"))
    args.output_dir.mkdir(parents=True,exist_ok=True)
    def save(name,data):
        (args.output_dir/name).write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
    save('w1-draft.json',rows)
    save('inventory.json',dict(edge_counts=counts, candidates=evidence, seconds=round(time.monotonic()-start,3)))
    save('graph.json',dict(graph={n:sorted(ds) for n,ds in graph.items()},model_mentions=sorted(mentions)))
    before=lc.analyze(graph,mentions,config)
    after=lc.analyze(renamed_graph(graph,{r['module']:r['dest'] for r in rows}),mentions,config)
    save('before.json',before);save('after.json',after)
    print(json.dumps(dict(candidates=len(proposals),move=len(rows),pending=len(proposals)-len(rows),
                          collisions=sorted(collisions),seconds=round(time.monotonic()-start,3)),ensure_ascii=False))

if __name__=='__main__': main()
