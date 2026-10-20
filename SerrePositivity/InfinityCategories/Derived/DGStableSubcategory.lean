module
public import SerrePositivity.InfinityCategories.Derived.DGStableSubcategoryChoices
public import SerrePositivity.InfinityCategories.Derived.DGFullSubcategoryNerve
public import SerrePositivity.InfinityCategories.Stable.ExactFunctorChoice
/-!
概要：実安定閉性を満たす充満 dg 部分圏の安定性と包含の完全性。
方針：同じ周囲の四角形を保つ双カルテジアンな選択を使う。
規約：実 ∞ 圏の安定性。使われ方：Verdier 列の左の完全充満忠実関手。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
variable [IsStable (dgNerve A D)] (P : D → Prop) (hP : DGStableObjectProperty A D P)
include hP
/-- 零・実 fiber・cofiber で閉じた全 dg 部分圏の nerve は安定。 -/
theorem dgStableSubcategory_isStable : IsStable (dgNerve A (DGFullSubcategory D P)) := by
  let := dgStableSubcategory_hasZeroVertex A D P hP
  apply isStable_of_bicartesian_choices (dgStableSubcategory_fiber_exists A D P hP)
  intro x y e
  obtain ⟨s, hs, _⟩ := dgStableSubcategory_cofiber_exists A D P hP e
  exact ⟨s, hs⟩
/-- 実安定閉性を満たす全 dg 部分圏の包含は完全。 -/
theorem dgStableSubcategoryInclusion_isExactFunctor :
    IsExactFunctor (dgNerve.map (dgFullSubcategoryInclusion A D P)) := by
  apply isExactFunctor_of_preserves_chosen_cofibers _ (dgFunctorNerve_preservesZeroVertices _)
  intro x y e
  obtain ⟨s, _, hs⟩ := dgStableSubcategory_cofiber_exists A D P hP e
  exact ⟨s, hs⟩
/-- 指定対象の実安定閉包からなる充満 dg 部分圏の nerve。 -/
abbrev dgStableClosureNerve (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
    (P : Set D) := dgNerve A (DGFullSubcategory D (dgStableClosureProperty A D P))
end SerrePositivity.InfinityCategories
