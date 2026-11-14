module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGUniversalCommaTarget
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorTrivialFibration
/-!
概要：普遍余単位の実 comma の標的 nerve 射影の厳密切断から、全単体上の逆作用を作る。
方針：実対象と全 Hom の各次数全射準同型性から自明 Kan fibration を得る。
規約：まだ ∞ 随伴の三角式は主張しない。使われ方：一般 RHom の coherent な実関手。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C E : Type (max (u + 1) v))
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
  (h : ∀ y : E, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalCounit R C E F y))
include h
/-- 同じ実 comma の標的 nerve 射影は自明 Kan fibration。 -/
lemma dgUniversalCommaTargetNerve_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaTarget R C E F)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_trivialKanFibration_of_surjective_quasiIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaTarget R C E F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaTarget_obj_surjective R C E F h)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaTarget_degree_surjective R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaTarget_map_quasiIso R C E F)
/-- 同じ標的射影とその厳密切断を持つ実 ∞ 圏同値。 -/
def dgUniversalCommaNerveEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalComma R C E F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) := by
  let := dgUniversalCommaTargetNerve_trivialKanFibration R C E F h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaTarget R C E F))
/-- 同じ実逆写像は、元の標的射影の全単体上の厳密切断。 -/
lemma dgUniversalCommaNerveEquivalence_inv_hom :
    (dgUniversalCommaNerveEquivalence R C E F h).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaTarget R C E F) = 𝟙 _ := by
  let := dgUniversalCommaTargetNerve_trivialKanFibration R C E F h
  exact Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaTarget R C E F)))
/-- 普遍余単位の厳密切断と実始域射影から得る、全単体上の右随伴候補。 -/
def dgUniversalRightAdjointCandidate : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C :=
  (dgUniversalCommaNerveEquivalence R C E F h).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalCommaSource R C E F)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
