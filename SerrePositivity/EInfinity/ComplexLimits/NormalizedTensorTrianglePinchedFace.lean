module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleOrdinaryFaces
/-! 概要：三角形の全境界を元の部分単体と比較する。
方針：同じ対象族と全 cochain の異種等号を等式へ戻す。
規約：元の K と全次数を保持。使われ方：大域評価三角形の三辺の同定。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet MonoidalCategory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)
lemma normalizedTensorTriangleSimplex_eq_pinched {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (h1 : ∀ i, τ i ≠ 1) :
    normalizedTensorTriangleSimplex A X Y c τ = normalizedTensorTrianglePinched A X Y c τ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply simplexData_ext_of_components
  · intro i
    by_cases hz : τ i = 0
    · exact (normalizedTensorTrianglePinched_obj_zero A X Y c τ i hz).symm
    · have ht : τ i = 2 := by have := h1 i; omega
      exact (normalizedTensorTrianglePinched_obj_two A X Y c τ i ht).symm
  · intro I a b k hI ha hb hk
    by_cases hb2 : τ b = 2
    · by_cases ha0 : τ a = 0
      · exact normalizedTensorTriangleData_hom_pinched A X Y c τ I a b k hI ha hb hk hb2 ha0
      · have ha2 : τ a = 2 := by have := h1 a; omega
        have h2 : ∀ i ∈ I, τ i = 2 := by
          intro i hi
          have hai : a ≤ i := by rw [ha]; exact I.min'_le i hi
          exact le_antisymm (Fin.le_last _) (ha2 ▸ τ.monotone hai)
        exact (normalizedTensorTriangleData_hom_back A X Y c τ I a b k hI ha hb hk hb2 ha0).trans
          (normalizedTensorTriangleBack_Pinched_two_hom A X Y c τ I a b k hI ha hb hk h2)
    · have hb0 : τ b = 0 := by have := h1 b; omega
      have h0 : ∀ i ∈ I, τ i = 0 := by
        intro i hi
        have hib : i ≤ b := by rw [hb]; exact I.le_max' i hi
        exact le_antisymm (hb0 ▸ τ.monotone hib) (Fin.zero_le _)
      exact (normalizedTensorTriangleData_hom_front A X Y c τ I a b k hI ha hb hk hb2).trans
        (normalizedTensorTriangleFront_Pinched_zero_hom A X Y c τ I a b k hI ha hb hk h0)
end SerrePositivity.EInfinity.ComplexLimits
