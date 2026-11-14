module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGRepleteYonedaEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveUniverseLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EquivalenceStability

/-! # 共通宇宙の前三角 dg nerve の安定性

概要：前三角 dg 圏の対象宇宙を上げた nerve と元の nerve の ULift は安定。
方針：ホモトピー表現可能部分との実同値で安定性を輸送し、実宇宙同型と合成する。
規約：元の小さい宇宙への降下は別工程。使われ方：β3 の前三角性からの安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 元の nerve の ULift とホモトピー表現可能部分の明示的 ∞ 圏同値。 -/
def dgRepleteYonedaULiftEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      ((SSet.uliftFunctor.{max (u + 1) v, max u v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentableNerve A D) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, v, max (u + 1) v} A D)).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteYonedaNerveEquivalence A D)

/-- 前三角 dg 圏の対象宇宙を上げた nerve は安定。 -/
lemma dgUniverseLiftNerve_isStable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, max (u + 1) v} D)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteYonedaNerveEquivalence A D).isStable_iff.mpr inferInstance

/-- 前三角 dg 圏の元の nerve を単体集合として ULift すると安定。 -/
lemma dgNerveULift_isStable_of_pretriangulated [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable ((SSet.uliftFunctor.{max (u + 1) v, max u v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)) :=
  (dgRepleteYonedaULiftEquivalence A D).isStable_iff.mpr inferInstance

/-- ホモトピー表現可能部分への実 Yoneda の nerve は完全。 -/
lemma dgRepleteYonedaNerve_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteYoneda A D)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteYonedaNerveEquivalence A D).isQCatEquivalence

/-- 選択された同値の逆写像も完全。 -/
lemma dgRepleteYonedaNerveInverse_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteYonedaNerveEquivalence A D).inv :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteYonedaNerveEquivalence A D).symm.isQCatEquivalence

end SerrePositivity.InfinityCategories.Project.DerivedCategories
