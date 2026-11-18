module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.SimplexDataLocalEquation
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleMiddle

/-!
概要：元の混合データは零相または二相を含まない任意部分集合で全 HA を満たす。
方針：全成分・全切断・微分の比較を端点の等式輸送と両立させる。
規約：元の実単体と同じ対象・次数を保持する。使われ方：大域評価三角形の全 HA。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorTriangleData_equation_front {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (h2 : ∀ i ∈ I, τ i ≠ 2) : (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ).Equation I := by
  apply _root_.SerrePositivity.ComplexLimits.simplexData_equation_of_agreementOn _ (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront A X Y c τ) I
  · intro i hi
    exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront_obj A X Y c τ i (h2 i hi)).symm
  · intro J hJI a b k hJ ha hb hk
    have hbJ : b ∈ J := by rw [hb]; exact J.max'_mem _
    exact _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_hom_front A X Y c τ J a b k hJ ha hb hk
      (h2 b (hJI hbJ))

lemma normalizedTensorTriangleData_equation_back {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (h0 : ∀ i ∈ I, τ i ≠ 0) : (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData A X Y c τ).Equation I := by
  apply _root_.SerrePositivity.ComplexLimits.simplexData_equation_of_agreementOn _ (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleBack A X Y c τ) I
  · intro i hi
    exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleBack_obj A X Y c τ i (h0 i hi)).symm
  · intro J hJI a b k hJ ha hb hk
    have haJ : a ∈ J := by rw [ha]; exact J.min'_mem _
    by_cases hbt : τ b = 2
    · exact _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_hom_back A X Y c τ J a b k hJ ha hb hk
        hbt (h0 a (hJI haJ))
    · have h2 : ∀ i ∈ J, τ i ≠ 2 := by
        intro i hi hti
        apply hbt
        have hib : i ≤ b := by rw [hb]; exact J.le_max' i hi
        exact le_antisymm (Fin.le_last _) (hti ▸ τ.monotone hib)
      exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_hom_front A X Y c τ J a b k hJ ha hb hk hbt).trans
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront_Back_hom A X Y c τ J a b k hJ ha hb hk
          (fun i hi => h0 i (hJI hi)) h2)
end SerrePositivity.ComplexLimits
