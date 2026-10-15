"""Check that reusable cochain and Adams contracts avoid concrete Adams implementations."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
graph = {
    '.'.join(path.relative_to(ROOT).with_suffix('').parts): re.findall(
        r'^(?:public\s+)?import\s+(SerrePositivity\.[\w.]+)',
        path.read_text(), re.MULTILINE)
    for path in (ROOT / 'SerrePositivity').rglob('*.lean')
}

def closure(start):
    seen, pending = set(), [start]
    while pending:
        module = pending.pop()
        if module not in seen:
            seen.add(module)
            pending.extend(graph.get(module, []))
    return seen

common = [name for name in graph if name.startswith(
    'SerrePositivity.HomologicalAlgebra.CochainTensor')]
common += ['SerrePositivity.HomologicalAlgebra.CochainBiproduct',
           'SerrePositivity.HomologicalAlgebra.CochainKernelLift',
           'SerrePositivity.HomologicalAlgebra.CochainIdempotent',
           'SerrePositivity.HomologicalAlgebra.KoszulOneCoordinates']
for name in common:
    forbidden = [dep for dep in closure(name)
                 if '.KTheory.' in dep or '.PerfectComplex.' in dep]
    assert not forbidden, (name, forbidden)

for name in ['Family', 'WeightOperators']:
    module = 'SerrePositivity.KTheory.Adams.' + name
    forbidden = [dep for dep in closure(module) if dep.startswith(
        'SerrePositivity.KTheory.Adams.') and dep.rsplit('.', 1)[-1].startswith(
            ('TensorSquare', 'TensorCube', 'CyclicTwo', 'CyclicThree', 'Cubic'))]
    assert not forbidden, (module, forbidden)
print(f'Import boundaries passed: {len(common)} cochain modules and 2 Adams contracts.')
