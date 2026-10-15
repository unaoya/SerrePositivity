"""Check that reusable cochain and Adams contracts avoid concrete Adams implementations."""
import argparse
from collections import deque
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
graph = {
    '.'.join(path.relative_to(ROOT).with_suffix('').parts): re.findall(
        r'^(?:public\s+)?import\s+(SerrePositivity\.[\w.]+)',
        path.read_text(), re.MULTILINE)
    for path in (ROOT / 'SerrePositivity').rglob('*.lean')
}

def dependency_path(start, forbidden):
    if start not in graph:
        raise SystemExit(f'Missing boundary entry point: {start}')
    seen, pending = {start}, deque([[start]])
    while pending:
        path = pending.popleft()
        module = path[-1]
        if module not in graph:
            raise SystemExit('Missing local import path:\n  ' + '\n  -> '.join(path))
        if forbidden(module):
            return path
        for dependency in graph[module]:
            if dependency not in seen:
                seen.add(dependency)
                pending.append(path + [dependency])
    return None


def check(start, forbidden):
    path = dependency_path(start, forbidden)
    if path:
        raise SystemExit('Forbidden import path:\n  ' + '\n  -> '.join(path))


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--consumers', action='store_true',
                    help='also enforce the consumer boundaries being migrated in R23–R24')
parser.add_argument('--cubic', action='store_true',
                    help='also enforce independence of the cubic family from the square operation')
args = parser.parse_args()


def upper_layer(module):
    return '.KTheory.' in module or '.PerfectComplex.' in module

common = [name for name in graph if name.startswith((
    'SerrePositivity.HomologicalAlgebra.CochainTensor',
    'SerrePositivity.HomologicalAlgebra.CochainCone',
    'SerrePositivity.HomologicalAlgebra.CochainIdempotent'))]
common += ['SerrePositivity.HomologicalAlgebra.CochainBiproduct',
           'SerrePositivity.HomologicalAlgebra.CochainAcyclic',
           'SerrePositivity.HomologicalAlgebra.CochainTwoTermScalarMap',
           'SerrePositivity.HomologicalAlgebra.CochainKernelLift',
           'SerrePositivity.HomologicalAlgebra.ProjectiveBaseChange',
           'SerrePositivity.HomologicalAlgebra.ModuleBaseChangeTensor',
           'SerrePositivity.HomologicalAlgebra.KoszulOneCoordinates']
for name in common:
    check(name, upper_layer)

for name in ['Family', 'WeightOperators']:
    module = 'SerrePositivity.KTheory.Adams.' + name
    check(module, lambda dep: dep.startswith('SerrePositivity.KTheory.Adams.') and
          dep.rsplit('.', 1)[-1].startswith(
              ('TensorSquare', 'TensorCube', 'CyclicTwo', 'CyclicThree', 'Cubic')))
print(f'Import boundaries passed: {len(common)} cochain modules and 2 Adams contracts.')

coefficient_comparison = {
    'SerrePositivity.KTheory.' + name for name in [
        'K0Localization', 'K0LocalizationCoefficients', 'G0Localization',
        'HomologyEuler', 'HomologyEulerBasic', 'HomologyPeeling', 'ComparisonInverse',
        'ComparisonNaturality']
} | {'SerrePositivity.PerfectComplex.IntegerEuler',
     'SerrePositivity.PerfectComplex.CoefficientEuler'}
for name in ['KTheory.SupportedCoefficients', 'KTheory.Adams.Family',
             'KTheory.Adams.WeightOperators', 'PerfectComplex.CubicActionClass']:
    check('SerrePositivity.' + name, lambda dep: dep in coefficient_comparison)
check('SerrePositivity.PerfectComplex.CubicActionClass',
      lambda dep: dep.startswith('SerrePositivity.KTheory.Adams.'))
print('Basic coefficient operations and contracts are independent of localization and Euler comparison.')

coefficient_foundations = {'SerrePositivity.KTheory.' + name for name in [
    'CoefficientExtension', 'CoefficientLinearExtension', 'CoefficientExactness']}
for name in sorted(coefficient_foundations):
    check(name, lambda dep: upper_layer(dep) and dep not in coefficient_foundations)
print('Coefficient extension and right exactness are independent of the K₀ and G₀ models.')

weight_decomposition = {'SerrePositivity.KTheory.Adams.' + name for name in [
    'WeightDecomposition', 'WeightAnnihilation', 'WeightDefectLift', 'SemilocalPureWeight']}
check('SerrePositivity.KTheory.Adams.WeightProduct',
      lambda dep: dep in weight_decomposition or dep in coefficient_comparison)
print('Products of eigenclasses are independent of weight decomposition and localization comparisons.')

check('SerrePositivity.PerfectComplex.CubicActionTensorProjectors',
      lambda dep: dep.startswith('SerrePositivity.PerfectComplex.Involution'))
print('Cubic tensor projectors are independent of involution implementations.')

check('SerrePositivity.PerfectComplex.InvolutionClassAcyclic',
      lambda dep: dep.startswith('SerrePositivity.KTheory.Adams.'))
print('The general acyclic involution class is independent of Adams implementations.')

check('SerrePositivity.PerfectComplex.IdempotentImageClass',
      lambda dep: dep in coefficient_comparison or
      dep.startswith('SerrePositivity.KTheory.Adams.'))
print('Idempotent image classes are independent of Adams and Euler/localization comparisons.')

check('SerrePositivity.PerfectComplex.DegreewiseRetract',
      lambda dep: '.KTheory.' in dep or dep in {
          'SerrePositivity.PerfectComplex.ClosedSupportK0',
          'SerrePositivity.CategoryTheory.TriangulatedK0'})
rank_one_ext = 'SerrePositivity.PerfectComplex.RankOneTensorTripleExt'
check(rank_one_ext, lambda dep: dep != rank_one_ext and upper_layer(dep))
print('Degreewise retracts and rank-one tensor extensionality avoid Grothendieck groups.')

general = ['AlternatingSum', 'FiniteSupportBounds', 'ExactImageSequence', 'HomotopyConeRepresentative',
           'HomotopyProperty', 'TriangulatedK0Shift']
for name in general:
    check('SerrePositivity.CategoryTheory.' + name, upper_layer)
check('SerrePositivity.KTheory.SupportedExactEuler',
      lambda dep: dep in {'SerrePositivity.KTheory.ResolutionClass',
                         'SerrePositivity.KTheory.ResolutionAdditivity'})
print(f'Euler and homotopy boundaries passed: {len(general)} general modules and the supported sequence.')

resolution_comparison = {'SerrePositivity.KTheory.' + name for name in [
    'ResolutionClass', 'ResolutionAdditivity', 'HomologyPeeling', 'ComparisonInverse']}
check('SerrePositivity.KTheory.HomologyEulerBasic', lambda dep: dep in resolution_comparison)
check('SerrePositivity.PerfectComplex.IntegerEuler', lambda dep: dep in resolution_comparison)
print('Basic homology and integer Euler evaluations are independent of resolution comparisons.')

for name in ['SupportedModule', 'G0Supported', 'MaximalSupportLength']:
    check('SerrePositivity.KTheory.' + name,
          lambda dep: '.PerfectComplex.' in dep or '.KTheory.Adams.' in dep or
          dep == 'SerrePositivity.CategoryTheory.TriangulatedK0')
print('Supported G₀ modules and closed-point length avoid perfect complexes and Adams implementations.')

maximal_length = ['G0Functoriality', 'MaximalSupportModules',
                  'MaximalSupportLocalLength', 'MaximalSupportLengthEquiv']
for name in maximal_length:
    check('SerrePositivity.KTheory.' + name,
          lambda dep: '.PerfectComplex.' in dep or '.KTheory.Adams.' in dep or dep in {
              'SerrePositivity.CommutativeAlgebra.SemilocalSupport',
              'SerrePositivity.CommutativeAlgebra.SupportHeight',
              'SerrePositivity.HomologicalAlgebra.Tor',
              'SerrePositivity.CategoryTheory.TriangulatedK0'})
print('General G₀ local lengths avoid height strata, Tor, and K₀ comparisons.')

geometry = ['ClosedSupportGeometry', 'ModuleClosedSupport', 'SupportHeight',
            'SemilocalSupport', 'ModuleSupportHeight', 'LocalizationTorsion', 'ModuleSupport',
            'PrincipalSupport', 'LocalizationLattice', 'SubmoduleExact']
for name in geometry:
    check('SerrePositivity.CommutativeAlgebra.' + name, upper_layer)
print(f'Support geometry boundaries passed: {len(geometry)} modules.')

check('SerrePositivity.CommutativeAlgebra.AlgebraAction', upper_layer)
print('Algebra action formulas are independent of the K₀ models.')

for name in ['FiniteFreeBaseChange', 'FiniteLocalizationDescent', 'LocalizedRegularResolution',
             'BoundedResolutionDimension', 'ResolutionMappingCone']:
    check('SerrePositivity.HomologicalAlgebra.' + name, upper_layer)
for name in ['PerfectComplex.FiniteProjectiveResolutions', 'CommutativeAlgebra.RegularLocalization']:
    check('SerrePositivity.' + name,
          lambda dep: '.KTheory.' in dep or dep in {
              'SerrePositivity.PerfectComplex.ClosedSupportK0',
              'SerrePositivity.CategoryTheory.TriangulatedK0'})
print('Localized resolution and regularity boundaries passed without Grothendieck groups.')

consumers = [
    'DifferentialGraded.Complexes.Braiding',
    'DifferentialGraded.Complexes.Biproduct',
    'DifferentialGraded.Complexes.AcyclicCone',
    'DifferentialGraded.Complexes.TensorShift',
    'DifferentialGraded.Complexes.ConeMaps',
    'DifferentialGraded.Complexes.Currying',
    'HomologicalAlgebra.BoundedAboveTensorModels',
    'HomologicalAlgebra.BoundedAboveDerivedAssociator',
    'HomologicalAlgebra.BoundedAboveDerivedBaseChange',
    'HomologicalAlgebra.DerivedTensorCoherenceModels',
    'HomologicalAlgebra.DerivedQuotientKoszul',
    'HomologicalAlgebra.TensorSingleNaturality',
    'HomologicalAlgebra.TensorConeNaturality',
    'HomologicalAlgebra.ScalarConeShiftNaturality',
]
if args.consumers:
    for name in consumers:
        check('SerrePositivity.' + name, upper_layer)
    print(f'Consumer boundaries passed: {len(consumers)} entry points.')

if args.cubic:
    # Raw squares and their coordinates are useful for a cube. Only the actual
    # degree-two operation and its additivity/multiplicativity layers are forbidden.
    square_operations = ('CyclicTwo', 'TensorSquareEvaluation', 'TensorSquareAdditivity',
                         'TensorSquareMultiplicativity', 'TensorSquareAcyclicClass')
    check('SerrePositivity.KTheory.Adams.CyclicThreeFamily',
          lambda dep: dep.startswith('SerrePositivity.KTheory.Adams.') and
          dep.rsplit('.', 1)[-1].startswith(square_operations))
    print('Cubic family is independent of the degree-two operation.')
