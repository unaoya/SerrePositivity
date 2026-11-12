#!/usr/bin/env python3
"""概要：Lean import グラフの層・禁止閉包を検査する（ビルド不要）。
方針：直接辺と推移閉包を分け、循環も SCC で完全に扱う。
規約：設定の例外以外で辺を隠さない。report は診断のみ、強制は明示する。
使われ方：--report / --enforce W1 / --ratchet previous-layers.json。
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict, deque
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import time

TIERS = ('W1', 'W2a', 'W2b')
IC = 'SerrePositivity.InfinityCategories'


def under(name, prefix):
    return name == prefix or name.startswith(prefix + '.')


def code_only(source):
    """Mask nested comments and strings; preserve offsets and line boundaries."""
    out = list(source)
    i, depth, string = 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2
            elif source.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if source[i] != '\n': out[i] = ' '
                i += 1
        elif string:
            if source[i] == '\\' and i + 1 < len(source):
                out[i] = ' '
                if source[i+1] != '\n': out[i+1] = ' '
                i += 2
            else:
                if source[i] == '"': string = False
                if source[i] != '\n': out[i] = ' '
                i += 1
        elif source.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2
        elif source.startswith('--', i):
            end = source.find('\n', i)
            if end == -1: end = len(source)
            out[i:end] = ' ' * (end-i); i = end
        elif source[i] == "'" and (literal := re.match(r"'(?:\\.|[^'\\\n])'", source[i:i+8])):
            end = i + len(literal[0]); out[i:end] = ' ' * (end-i); i = end
        elif source[i] == '"':
            out[i] = ' '; string = True; i += 1
        else:
            i += 1
    if depth or string:
        raise ValueError('unterminated Lean comment or string')
    return ''.join(out)


def imports(source):
    result = set()
    clean = code_only(source)
    boundary = set('module prelude import public private meta open namespace section end def abbrev opaque theorem lemma example instance inductive structure class variable variables universe universes noncomputable set_option attribute export initialize builtin_initialize syntax macro macro_rules elab deriving in include omit axiom constant mutual local scoped'.split())
    for match in re.finditer(r'(?m)^[ \t]*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?', clean):
        position, count = match.end(), 0
        while token := re.match(r'\s*([\w\u0080-\uffff]+(?:\.[\w\u0080-\uffff]+)*)', clean[position:]):
            name = token[1]
            if name in boundary: break
            result.add(name); count += 1; position += token.end()
        if not count: raise ValueError('import has no supported module name')
    return result


def read_graph(root, config):
    graph, model_mentions = {}, set()
    rule = config['model_category_rule']
    for directory, dirs, files in os.walk(root):
        dirs[:] = sorted(d for d in dirs if not d.startswith('.') and d != 'node_modules')
        for filename in sorted(files):
            if not filename.endswith('.lean'): continue
            path = Path(directory) / filename
            name = '.'.join(path.relative_to(root).with_suffix('').parts)
            source = path.read_text()
            try:
                graph[name] = imports(source)
                if under(name, rule['prefix']) and rule['code_contains'] in code_only(source):
                    model_mentions.add(name)
            except ValueError as exc:
                raise ValueError(f'{path}: {exc}') from exc
    return graph, model_mentions


def validate_config(config):
    names, prefixes = set(), set()
    for layer in config['layers']:
        if layer['name'] in names: raise ValueError('duplicate layer')
        names.add(layer['name'])
        if not isinstance(layer['rank'], int): raise ValueError('non-integer rank')
        for prefix in layer['prefixes']:
            if prefix in prefixes: raise ValueError('duplicate layer prefix')
            prefixes.add(prefix)
    if not set(config['core']).issubset(names): raise ValueError('unknown core layer')
    for rule in config['restricted_imports']:
        if rule not in names: raise ValueError('unknown restricted layer')
    for exception in config['exceptions']:
        if set(exception) != {'from', 'to', 'reason', 'expires'} or not exception['reason'].strip():
            raise ValueError('exception requires from, to, reason, expires')
        if exception['expires'] not in TIERS: raise ValueError('unknown exception expiry')


def classify(name, config):
    matches = [(len(p), layer['name']) for layer in config['layers']
               for p in layer['prefixes'] if under(name, p)]
    return max(matches)[1] if matches else None


def group(name, config):
    layer = classify(name, config)
    if layer: return layer
    if name.startswith('SerrePositivity.'):
        return '.'.join(name.split('.')[:2])
    return name.split('.')[0]


def closure_masks(graph):
    """Transitive dependency bitsets, iterative Kosaraju + sink-first SCC DAG.

    External packages are terminal vertices. Their sources are not repository files.
    Including the root itself makes cycles and shared dependencies unambiguous.
    """
    nodes = sorted(set(graph).union(*(set(v) for v in graph.values())))
    index = {n: i for i, n in enumerate(nodes)}
    adj = [[index[d] for d in sorted(graph.get(n, ()))] for n in nodes]
    reverse = [[] for _ in nodes]
    for i, ds in enumerate(adj):
        for d in ds: reverse[d].append(i)
    visited, order = set(), []
    for first in range(len(nodes)):
        if first in visited: continue
        visited.add(first); stack = [(first, iter(adj[first]))]
        while stack:
            v, children = stack[-1]
            child = next(children, None)
            if child is None:
                order.append(v); stack.pop()
            elif child not in visited:
                visited.add(child); stack.append((child, iter(adj[child])))
    components, membership = [], {}
    for first in reversed(order):
        if first in membership: continue
        component = len(components)
        membership[first] = component; pending = [first]; members = []
        while pending:
            v = pending.pop(); members.append(v)
            for parent in reverse[v]:
                if parent not in membership:
                    membership[parent] = component; pending.append(parent)
        components.append(members)
    deps = [set() for _ in components]
    parents = [set() for _ in components]
    masks = [sum(1 << v for v in members) for members in components]
    for v, ds in enumerate(adj):
        a = membership[v]
        for d in ds:
            b = membership[d]
            if a != b: deps[a].add(b); parents[b].add(a)
    remaining = [len(ds) for ds in deps]
    queue = deque(i for i, n in enumerate(remaining) if n == 0)
    while queue:
        child = queue.popleft()
        for parent in parents[child]:
            masks[parent] |= masks[child]
            remaining[parent] -= 1
            if remaining[parent] == 0: queue.append(parent)
    return nodes, index, {n: masks[membership[i]] for n, i in index.items()}


def selected_names(mask, nodes):
    result = []
    while mask:
        bit = mask & -mask
        result.append(nodes[bit.bit_length()-1]); mask ^= bit
    return result


def forbidden(name, tier, config, model_mentions):
    prefixes = list(config['forbidden']['W1'])
    if tier != 'W1':
        if any(under(name, prefix) for prefix in config['allowed_until_move']): return False
        prefixes += config['forbidden']['W2a_additions']
        if name in model_mentions: return True
    return any(under(name, p) for p in prefixes)


def direct_reasons(src, dst, config):
    a, b = classify(src, config), classify(dst, config)
    if not a: return []
    reasons = []
    ranks = {layer['name']: layer['rank'] for layer in config['layers']}
    if b and ranks[b] > ranks[a]: reasons.append('upward-layer-import')
    restriction = config['restricted_imports'].get(a)
    if restriction and b not in restriction['layers'] and not any(
            under(dst, p) for p in restriction['external_prefixes']):
        reasons.append('restricted-layer-import')
    return reasons


def analyze(graph, model_mentions, config):
    validate_config(config)
    config_hash = hashlib.sha256(json.dumps(config, sort_keys=True).encode()).hexdigest()
    classified = {n: classify(n, config) for n in graph}
    core = sorted(n for n, layer in classified.items() if layer in config['core'])
    # Layer entry files (Core.lean, Stable.lean, ...) are distinguished from leaves.
    entries = {p for layer in config['layers'] for p in layer['prefixes']}
    leaves = [n for n in core if n not in entries]
    unknown = defaultdict(list)
    for n, layer in sorted(classified.items()):
        if layer is None:
            directory = n.rsplit('.', 1)[0] if '.' in n else '<root>'
            unknown[directory].append(n)
    violations = []
    for src in sorted(graph):
        for dst in sorted(graph[src]):
            reasons = direct_reasons(src, dst, config)
            bans = [t for t in TIERS if src in classified and classified[src] in config['core']
                    and forbidden(dst, t, config, model_mentions)]
            if reasons or bans:
                violations.append({'from': src, 'to': dst, 'from_layer': group(src, config),
                                   'to_layer': group(dst, config), 'rules': reasons,
                                   'forbidden_tiers': bans})
    pair_counts = Counter(f"{v['from_layer']} -> {v['to_layer']}" for v in violations)
    nodes, index, raw_masks = closure_masks(graph)
    repo_mask = sum(1 << index[n] for n in graph if under(n, 'SerrePositivity'))
    core_mask = sum(1 << index[n] for n in core)
    def external(roots):
        mask = 0
        for n in roots: mask |= raw_masks[n]
        names = selected_names(mask & repo_mask & ~core_mask, nodes)
        return {'count': len(names), 'by_group': dict(sorted(Counter(group(n, config) for n in names).items())),
                'modules': names}
    tiers, metrics = {}, {}
    for tier in TIERS:
        exceptions = {(e['from'], e['to']) for e in config['exceptions']
                      if TIERS.index(tier) <= TIERS.index(e['expires'])}
        effective = {n: {d for d in ds if (n, d) not in exceptions} for n, ds in graph.items()}
        if exceptions:
            tier_nodes, tier_index, masks = closure_masks(effective)
        else:
            tier_nodes, tier_index, masks = nodes, index, raw_masks
        forbidden_names = [n for n in tier_nodes if forbidden(n, tier, config, model_mentions)]
        banned_mask = sum(1 << tier_index[n] for n in forbidden_names)
        union, by_module, by_layer_masks = 0, {}, defaultdict(int)
        for n in core:
            reached = masks[n] & banned_mask
            by_module[n] = reached.bit_count()
            union |= reached; by_layer_masks[classified[n]] |= reached
            metrics[f'closure/{tier}/{n}'] = by_module[n]
        reached_names = selected_names(union, tier_nodes)
        ingress = [{'from': n, 'to': d} for n in core for d in sorted(effective[n])
                   if forbidden(d, tier, config, model_mentions)]
        enforced_direct = [v for v in violations if (v['from'], v['to']) not in exceptions
                           and classified.get(v['from']) in config['core']
                           and (tier in v['forbidden_tiers'] or (tier == 'W2b' and v['rules']))]
        direct_counts = Counter(f"{v['from_layer']} -> {v['to_layer']}" for v in enforced_direct)
        tiers[tier] = {'forbidden_module_count': len(reached_names), 'forbidden_modules': reached_names,
                       'affected_core_module_count': sum(bool(v) for v in by_module.values()),
                       'closure_pair_count': sum(by_module.values()), 'by_module': by_module,
                       'by_layer': {k: v.bit_count() for k, v in sorted(by_layer_masks.items())},
                       'by_group': dict(sorted(Counter(group(n, config) for n in reached_names).items())),
                       'entry_edges': ingress, 'direct_violation_count': len(enforced_direct),
                       'direct_by_pair': dict(sorted(direct_counts.items())),
                       'violation_count': sum(by_module.values()) + len(enforced_direct)}
        metrics[f'closure_unique/{tier}'] = len(reached_names)
        metrics[f'entry_edges/{tier}'] = len(ingress)
        for pair, count in direct_counts.items(): metrics[f'direct/{tier}/{pair}'] = count
    for pair, count in pair_counts.items(): metrics[f'report_direct/{pair}'] = count
    ic_kst = sum(under(n, IC) and under(d, 'SerrePositivity.KST') for n, ds in graph.items() for d in ds)
    return {'schema_version': 1, 'config_sha256': config_hash,
            'module_count': len(graph), 'edge_count': sum(map(len, graph.values())),
            'core_module_count': len(core), 'core_leaf_count': len(leaves),
            'ic_to_kst_edge_count': ic_kst, 'direct_violations': violations,
            'direct_by_pair': dict(sorted(pair_counts.items())),
            'external_closure_all_core': external(core), 'external_closure_core_leaves': external(leaves),
            'tiers': tiers, 'unclassified_directories': dict(unknown),
            'ratchet_metrics': dict(sorted(metrics.items()))}


def ratchet_increases(current, baseline):
    if baseline['schema_version'] != current['schema_version'] or baseline['config_sha256'] != current['config_sha256']:
        raise ValueError('ratchet baseline schema/config differs; coordinator review required')
    old = baseline['ratchet_metrics']
    if not isinstance(old, dict) or not old: raise ValueError('missing baseline metrics')
    return [{'metric': k, 'before': old.get(k, 0), 'after': value}
            for k, value in current['ratchet_metrics'].items() if value > old.get(k, 0)]



def enforce_w2b(report, baseline, config):
    """IF-W2b §12: order, existing direct edges, and aggregate closure bounds.

    Per-root ratchet metrics remain diagnostic until the W2c paths are removed.
    This does not change ratchet_increases or the layer exception configuration.
    """
    if baseline['config_sha256'] != report['config_sha256']:
        raise ValueError('W2b baseline config differs; coordinator review required')
    core = set(config['core'])
    order = [e for e in report['direct_violations']
             if e['from_layer'] in core and e['to_layer'] in core
             and 'upward-layer-import' in e['rules']]
    allowed = {(e['from'], e['to']) for e in baseline['direct_edges']}
    unexpected = [e for e in report['direct_violations']
                  if e not in order and (e['from'], e['to']) not in allowed]
    increases = []
    for tier in ('W1', 'W2a'):
        for metric in ('forbidden_module_count', 'affected_core_module_count'):
            limit = baseline['aggregate_limits'][tier][metric]
            value = report['tiers'][tier][metric]
            if value > limit:
                increases.append({'tier': tier, 'metric': metric,
                                  'before': limit, 'after': value})
    return {'status': 'FAIL' if order or unexpected or increases else 'PASS',
            'core_order_violations': order, 'new_direct_edges': unexpected,
            'aggregate_increases': increases,
            'accepted_direct_edge_limit': len(allowed),
            'per_root_metrics': 'diagnostic (IF-W2b §12; ratchet is unchanged)'}


def print_report(report):
    print(f"modules={report['module_count']} edges={report['edge_count']} core={report['core_module_count']}")
    print('Direct violations by layer pair (distinct edges, before exceptions):')
    for pair, count in report['direct_by_pair'].items(): print(f'  {pair}: {count}')
    for tier, value in report['tiers'].items():
        print(f"{tier}: forbidden unique={value['forbidden_module_count']}; affected core={value['affected_core_module_count']}; closure pairs={value['closure_pair_count']}; direct={value['direct_violation_count']}")
        print('  forbidden groups:', json.dumps(value['by_group'], ensure_ascii=False))
        print(f"  Entry edges ({len(value['entry_edges'])}):")
        for e in value['entry_edges']: print(f"    {e['from']} -> {e['to']}")
    for k in ['external_closure_all_core', 'external_closure_core_leaves']:
        print(k, report[k]['count'], json.dumps(report[k]['by_group'], ensure_ascii=False))
    print('IC -> KST direct edges:', report['ic_to_kst_edge_count'])
    print('Unclassified modules by directory (all members in JSON):')
    for directory, names in report['unclassified_directories'].items(): print(f'  {directory}: {len(names)}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--report', action='store_true')
    mode.add_argument('--enforce', choices=(*TIERS, 'KLW1'))
    mode.add_argument('--ratchet', type=Path)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--config', type=Path, default=Path(__file__).with_name('layers.json'))
    parser.add_argument('--output', type=Path, help='default: ROOT/.lake/verify/layers.json')
    parser.add_argument('--w2b-baseline', type=Path,
                        default=Path(__file__).with_name('targets') / 'w2b-enforcement-baseline.json',
                        help='approved direct edges and pre-W2b aggregate limits for --enforce W2b')
    args = parser.parse_args()
    started = time.monotonic()
    try:
        config = json.loads(args.config.read_text())
        if args.enforce == 'KLW1' or (args.report and 'klw1' in config):
            from klw1_layer_check import check, source_graph
            profile = config['klw1']
            result = check(source_graph(args.root.resolve(), profile.get('exclude_prefixes', [])), profile)
            failed = bool(args.enforce and result['violations'])
            result.update(mode='enforce' if args.enforce else 'report',
                          status='FAIL' if failed else 'PASS' if args.enforce else 'REPORT',
                          seconds=round(time.monotonic()-started, 3))
            output = args.output or args.root / '.lake/verify/layers.json'
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n')
            print(f"KL-W1 {result['status']}: {len(result['violations'])} violations -> {output}")
            return int(failed)
        graph, mentions = read_graph(args.root.resolve(), config)
        result = analyze(graph, mentions, config)
        increases = ratchet_increases(result, json.loads(args.ratchet.read_text())) if args.ratchet else []
        w2b = (enforce_w2b(result, json.loads(args.w2b_baseline.read_text()), config)
               if args.enforce == 'W2b' else None)
        failed = bool(increases or (w2b['status'] == 'FAIL' if w2b is not None else
                                   args.enforce and result['tiers'][args.enforce]['violation_count']))
        if w2b is not None:
            result['w2b_enforcement'] = w2b
            result['w2b_baseline'] = str(args.w2b_baseline)
        result.update(mode='enforce' if args.enforce else 'ratchet' if args.ratchet else 'report',
                      enforced_tier=args.enforce, ratchet_increases=increases,
                      status='FAIL' if failed else 'REPORT' if args.report else 'PASS',
                      seconds=round(time.monotonic()-started, 3))
        output = args.output or args.root / '.lake/verify/layers.json'
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n')
        print_report(result)
        if w2b is not None: print('W2b contract:', json.dumps(w2b, ensure_ascii=False))
        for item in increases: print('INCREASE', json.dumps(item, ensure_ascii=False))
        print(f"{result['status']} ({result['seconds']}s) -> {output}")
        return int(failed)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f'layer_check: error: {exc}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
