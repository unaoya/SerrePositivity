"""個別の人手判断と、実行済みkernel検査の証拠を統合する。未確認を自動承認しない。"""
import collections
import csv
import importlib.util
import json
from pathlib import Path

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[3]
spec = importlib.util.spec_from_file_location('audit', BASE / 'check_declarations.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
with (ROOT / 'research/kerodon-coverage/items.csv').open() as f:
    items = [r for r in csv.DictReader(f) if r['number'].startswith('1.')]
decisions = json.loads((BASE / 'ch1-semantic-decisions.json').read_text())['items']
assert len(items) == len(decisions) == 180
verified = {}
for run in ['all-20261107-01', 'ch1-20261107-01', 'ch1-name-probes-01', 'ch1-name-probes-02', 'ch1-name-probes-03', 'ch1-name-probes-04', 'ch1-name-probes-05']:
    directory = BASE / 'runs' / run
    plan = json.loads((directory / 'plan.json').read_text())
    refs = {r['id']: r for r in plan['references']}
    for f in (directory / 'modules').glob('*/execution.json'):
        execution = json.loads(f.read_text())
        if execution['state'] != 'checked':
            continue
        parsed = audit.parse_output(f.with_name('lean.stdout.jsonl').read_text(), f.with_name('lean.stderr.txt').read_text(), execution['lean_returncode'], json.loads(f.with_name('commands.json').read_text()))
        for key, result in parsed.items():
            if result['state'] == 'found':
                ref = refs[key]
                verified[(ref['declaration'], ref['source'])] = dict(ref, result=result, evidence=str(f.parent.relative_to(ROOT)))

special = {
    'SimplexCategory.mk (⦋n⦌)': ['SimplexCategory.mk'],
    '記法 X _⦋n⦌': ['CategoryTheory.SimplicialObject'],
    'X _⦋n⦌（単体）, X _⦋0⦌（頂点）': ['SSet'],
    'SSet.yonedaEquiv.symm': ['SSet.yonedaEquiv'],
    'instance (Functor.const J).Full [IsConnected J]': ['CategoryTheory.instFullFunctorConstOfIsConnected'],
    '記法 |X|': ['SSet.toTop'],
    'instance SSet.toTop.IsLeftAdjoint': ['sSetTopAdj'],
    'MonCat.toCat (toCat_full, toCat_faithful)': ['MonCat.toCat_full', 'MonCat.toCat_faithful'],
    'SerrePositivity.KST.Comparison.monoidWordSimplex / monoidWordLabels': ['SerrePositivity.KST.Comparison.monoidWordSimplex', 'SerrePositivity.KST.Comparison.monoidWordLabels'],
    'instance KanComplex X.op': ['SSet.instKanComplexOp'],
    'HomotopicL.refl/symm/trans': ['SSet.Truncated.HomotopicL.' + n for n in ['refl', 'symm', 'trans']],
    'SSet.Truncated.Quasicategory₂ (fill21)': ['SSet.Truncated.Quasicategory₂.fill21'],
    'instance Quasicategory₂ (truncation 2 X)': ['SSet.instQuasicategory₂ObjTruncatedOfNatNatTruncationOfQuasicategory'],
    'instance Quasicategory₂ (truncation 2)': ['SSet.instQuasicategory₂ObjTruncatedOfNatNatTruncationOfQuasicategory'],
    'instance Category (HomotopyCategory₂ A)': ['SSet.Truncated.instCategoryHomotopyCategory₂'],
    'SSet（射 X ⟶ Y）': ['SSet'],
    'instance Quasicategory ((ihom A).obj X)': ['SSet.instQuasicategoryObjIhom'],
    'instance InnerFibration (terminal.from X)': ['SSet.instInnerFibrationFromOfQuasicategory'],
    'SSet.Subcomplex.Skeleton.isPushout': ['SSet.relativeCellComplexOfMono.isPushout'],
    'SSet.horn.desc': ['SSet.horn.IsCompatible.desc'],
    'SerrePositivity.InfinityCategories.HomotopyCategory.bridge_naturality': ['SerrePositivity.InfinityCategories.HomotopyCategoryMap.bridge_naturality'],
    'SerrePositivity.InfinityCategories.F1.compositionTriangleSpace_isContractibleKan': ['SerrePositivity.InfinityCategories.compositionTriangleSpace_isContractibleKan'],
}
extras = {
    '1.1.3.8': ['SSet.unique_nonDegenerate_dim'],
    '1.2.5.10': ['SerrePositivity.InfinityCategories.Kan.KanHomotopyZero.equivPiZero'],
    '1.3.2.8': ['Semigrp', 'MulHom'],
    '1.4.4.2': ['SSet.Truncated.Edge.CompStruct.nonempty_iff'],
    '1.5.3.4': ['CategoryTheory.nerveFunctorCompHoFunctorIso'],
}
rows, evidence_rows, missing = [], [], []
for item in items:
    number = item['number']
    decision = decisions[number]
    wanted = []
    for raw in item['declarations'].split(' | '):
        if not raw:
            continue
        old = audit.reference(raw)
        name = raw.split(' @ ')[0]
        if number == '1.1.3.9' and name == 'SSet.S':
            continue
        if number == '1.4.6.12' and name.endswith('simplicialFundamentalGroupoid'):
            continue
        if number == '1.5.7.1':
            continue
        names = special.get(name, [old['declaration'] or name])
        for n in names:
            direct = verified.get((n, old['source']))
            candidates = [v for (cn, source), v in verified.items() if source == old['source'] and cn.split('.')[-1] == n.split('.')[-1]]
            selected = direct or (candidates[0] if len(candidates) == 1 else None)
            wanted.append((selected, n, raw))
    added = list(extras.get(number, []))
    if number == '1.5.7.1':
        added += ['SerrePositivity.InfinityCategories.F2.Presentable.sequentialSpine_inclusion_innerAnodyne', 'SerrePositivity.InfinityCategories.trivialKanFibration_pre_of_innerAnodyne']
    for n in added:
        candidates = [v for (cn, _), v in verified.items() if cn == n]
        wanted.append((candidates[0] if candidates else None, n, '追加出典'))
    citations, axioms, unresolved = [], set(), []
    for ref, name, original in wanted:
        if ref is None:
            unresolved.append(name)
            citations.append(original if original != '追加出典' else name)
            missing.append(dict(number=number, declaration=name, original=original))
            continue
        citation = f"{ref['declaration']} @ {ref['source']}" + (f":{ref['source_line']}" if ref['source_line'] else '')
        if citation not in citations:
            citations.append(citation)
        axioms.update(ref['result']['extra_axioms'])
        evidence_rows.append(dict(number=number, declaration=ref['declaration'], source=ref['source'], evidence=ref['evidence'], type=ref['result']['type'], axioms=ref['result']['axioms']))
    declarations = ' | '.join(citations)
    changed = declarations != item['declarations']
    verdict = decision['verdict']
    reason = decision['reason']
    if unresolved:
        verdict = 'unsure'
        reason += ' kernel確認未解決: ' + '、'.join(unresolved)
    elif changed and verdict == 'ok':
        verdict = 'fix'
        reason += ' 宣言名・出典表記も検査済みの形に補正。'
    check = 'not_found' if not wanted or unresolved else 'renamed' if changed else 'found'
    rows.append(dict(number=number, verdict=verdict, status_new=decision['status_new'], declarations_new=declarations, reason=reason, axioms=' | '.join(sorted(axioms)), check=check))
assert [r['number'] for r in rows] == [r['number'] for r in items]
with (BASE / 'ch1-draft.csv').open('w', newline='') as f:
    w = csv.DictWriter(f, ['number','verdict','status_new','declarations_new','reason','axioms','check'], lineterminator='\n'); w.writeheader(); w.writerows(rows)
audit.dump(BASE / 'ch1-kernel-evidence.json', evidence_rows)
audit.dump(BASE / 'ch1-kernel-missing.json', missing)
print('verdicts', dict(collections.Counter(r['verdict'] for r in rows)))
print('checks', dict(collections.Counter(r['check'] for r in rows)))
print('missing kernel evidence', missing)
