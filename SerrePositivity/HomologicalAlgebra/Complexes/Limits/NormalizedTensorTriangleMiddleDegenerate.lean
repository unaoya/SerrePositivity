module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleNoninjectiveCuts

/-!
概要：両方の切断点が中央相にある主場合を除き、元の中央相の全切断和を比較する。
方針：元の非単射添字・同相の二点・切断の一意性を使う。
規約：主場合の非零成分比較は別工程。使われ方：大域評価三角形の混合 HA。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorTriangle_middle_sum_heq_of_not_both {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hc : 3 ≤ I.card) (a b : Fin (n + 1)) (k : ℤ)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (haz : τ a = 0) (hbt : τ b = 2)
    (hn : ¬ (τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI) = 1 ∧ τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI) = 1)) :
    HEq (∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (fun j => τ j = 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ).cutCompose I a b k j)
      (∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (fun j => τ j = 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched A X Y c τ).toSimplexData.cutCompose I a b k j) := by
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_middle_sum A X Y c τ I hI hc a b k ha hb hbt,
    _root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched_middle_sum A X Y c τ I hI hc a b k ha hb]
  have hx := (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched_obj_zero A X Y c τ a haz).symm
  have hy := (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched_obj_two A X Y c τ b hbt).symm
  have hsp := τ.monotone (_root_.SerrePositivity.ComplexLimits.second_le_penultimate I hI hc)
  by_cases hp1 : τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI) = 1
  · by_cases hs1 : τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI) = 1
    · exact False.elim (hn ⟨hs1, hp1⟩)
    · have hs0 : τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI) = 0 := by omega
      rw [ite_eq_left hp1, ite_eq_right hs1,
        _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_penultimate_zero_of_second_zero
          A X Y c τ I hI hc a b k ha haz hs0 hp1, smul_zero]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq hx hy rfl
  · rw [ite_eq_right hp1]
    by_cases hs1 : τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI) = 1
    · have hp2 : τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI) = 2 := by omega
      rw [ite_eq_left hs1,
        _root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched_second_zero_of_penultimate_two
          A X Y c τ I hI hc a b k hb hbt hs1 hp2, smul_zero]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq hx hy rfl
    · rw [ite_eq_right hs1]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq hx hy rfl
end SerrePositivity.ComplexLimits
