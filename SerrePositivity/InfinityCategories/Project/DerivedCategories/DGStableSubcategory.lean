module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStableSubcategoryChoices
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFullSubcategoryNerve
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorChoice
/-!
概要：実安定閉性を満たす充満 dg 部分圏の安定性と包含の完全性。
方針：同じ周囲の四角形を保つ双カルテジアンな選択を使う。
規約：実 ∞ 圏の安定性。使われ方：Verdier 列の左の完全充満忠実関手。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)] (P : D → Prop) (hP : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStableObjectProperty A D P)
include hP
/-- 零・実 fiber・cofiber で閉じた全 dg 部分圏の nerve は安定。 -/
theorem dgStableSubcategory_isStable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory D P)) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableSubcategory_hasZeroVertex A D P hP
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_of_bicartesian_choices (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableSubcategory_fiber_exists A D P hP)
  intro x y e
  obtain ⟨s, hs, _⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableSubcategory_cofiber_exists A D P hP e
  exact ⟨s, hs⟩
/-- 実安定閉性を満たす全 dg 部分圏の包含は完全。 -/
theorem dgStableSubcategoryInclusion_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P)) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_preserves_chosen_cofibers _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_preservesZeroVertices _)
  intro x y e
  obtain ⟨s, _, hs⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableSubcategory_cofiber_exists A D P hP e
  exact ⟨s, hs⟩
/-- 指定対象の実安定閉包からなる充満 dg 部分圏の nerve。 -/
abbrev dgStableClosureNerve (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
    (P : Set D) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty A D P))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
