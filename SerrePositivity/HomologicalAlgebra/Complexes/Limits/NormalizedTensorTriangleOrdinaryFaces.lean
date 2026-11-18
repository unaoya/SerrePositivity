module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.SimplexDataComponentExt
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleMap
/-! 概要：三角形の全境界を元の部分単体と比較する。
方針：同じ対象族と全 cochain の異種等号を等式へ戻す。
規約：元の K と全次数を保持。使われ方：大域評価三角形の三辺の同定。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)
lemma normalizedTensorTriangleSimplex_eq_front {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (h2 : ∀ i, τ i ≠ 2) :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleSimplex A X Y c τ = _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront A X Y c τ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.ComplexLimits.simplexData_ext_of_components
  · intro i
    exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront_obj A X Y c τ i (h2 i)).symm
  · intro I a b k hI ha hb hk
    exact _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_hom_front A X Y c τ I a b k hI ha hb hk (h2 b)
lemma normalizedTensorTriangleSimplex_eq_back {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (h0 : ∀ i, τ i ≠ 0) :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleSimplex A X Y c τ = _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleBack A X Y c τ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.ComplexLimits.simplexData_ext_of_components
  · intro i
    exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleBack_obj A X Y c τ i (h0 i)).symm
  · intro I a b k hI ha hb hk
    by_cases hb2 : τ b = 2
    · exact _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_hom_back A X Y c τ I a b k hI ha hb hk hb2 (h0 a)
    · have h2 : ∀ i ∈ I, τ i ≠ 2 := by
        intro i hi ht
        apply hb2
        have hib : i ≤ b := by rw [hb]; exact I.le_max' i hi
        exact le_antisymm (Fin.le_last _) (ht ▸ τ.monotone hib)
      exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleData_hom_front A X Y c τ I a b k hI ha hb hk hb2).trans
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleFront_Back_hom A X Y c τ I a b k hI ha hb hk
          (fun i _ => h0 i) h2)

end SerrePositivity.ComplexLimits
