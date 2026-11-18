module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleOrdinaryEquation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleConstantOverlap

/-!
概要：中央相を含まない任意部分集合で元の実三相データの全 HA を証明する。
方針：元の定値引き戻し・全 cochain・全削除和を端点の等式輸送と両立させる。
規約：混合二次境界の比較は別工程。使われ方：大域評価三角形の残る HA。
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

lemma normalizedTensorTriangleData_equation_pinched {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (h1 : ∀ i ∈ I, τ i ≠ 1) : (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ).Equation I := by
  apply _root_.SerrePositivity.ComplexLimits.simplexData_equation_of_agreementOn _ (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched A X Y c τ) I
  · intro i hi
    by_cases hz : τ i = 0
    · exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched_obj_zero A X Y c τ i hz).symm
    · have ho := h1 i hi
      have ht : τ i = 2 := by omega
      exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched_obj_two A X Y c τ i ht).symm
  · intro J hJI a b k hJ ha hb hk
    have haJ : a ∈ J := by rw [ha]; exact J.min'_mem _
    have hbJ : b ∈ J := by rw [hb]; exact J.max'_mem _
    by_cases hbt : τ b = 2
    · by_cases haz : τ a = 0
      · exact _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_hom_pinched A X Y c τ J a b k hJ ha hb hk hbt haz
      · have hao := h1 a (hJI haJ)
        have hat : τ a = 2 := by omega
        have h2 : ∀ i ∈ J, τ i = 2 := by
          intro i hi
          have hai : a ≤ i := by rw [ha]; exact J.min'_le i hi
          exact le_antisymm (Fin.le_last _) (hat ▸ τ.monotone hai)
        exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_hom_back A X Y c τ J a b k hJ ha hb hk hbt haz).trans
          (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleBack_Pinched_two_hom A X Y c τ J a b k hJ ha hb hk h2)
    · have hbo := h1 b (hJI hbJ)
      have hbz : τ b = 0 := by omega
      have h0 : ∀ i ∈ J, τ i = 0 := by
        intro i hi
        have hib : i ≤ b := by rw [hb]; exact J.le_max' i hi
        exact le_antisymm (hbz ▸ τ.monotone hib) (Fin.zero_le _)
      exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_hom_front A X Y c τ J a b k hJ ha hb hk hbt).trans
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront_Pinched_zero_hom A X Y c τ J a b k hJ ha hb hk h0)

end SerrePositivity.ComplexLimits
