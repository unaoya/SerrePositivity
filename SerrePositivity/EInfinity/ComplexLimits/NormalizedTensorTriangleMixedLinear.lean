module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleOrdinaryEquation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryDecomposition

/-!
概要：零から二への混合 cochain と全線形境界を元の pinched 単体へ戻す。
方針：元の定値引き戻し・全 cochain・全削除和を端点の等式輸送と両立させる。
規約：混合二次境界の比較は別工程。使われ方：大域評価三角形の残る HA。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorTriangleData_homOrZero_pinched {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hbt : τ b = 2) (haz : τ a = 0) :
    HEq ((normalizedTensorTriangleData A X Y c τ).homOrZero I a b k)
      ((normalizedTensorTrianglePinched A X Y c τ).toSimplexData.homOrZero I a b k) := by
  have hx := (normalizedTensorTrianglePinched_obj_zero A X Y c τ a haz).symm
  have hy := (normalizedTensorTrianglePinched_obj_two A X Y c τ b hbt).symm
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero
  split_ifs with hI ha hb hk
  · exact normalizedTensorTriangleData_hom_pinched A X Y c τ I a b k hI ha hb hk hbt haz
  all_goals exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq hx hy rfl

lemma normalizedTensorTriangleData_linearBoundary_pinched {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hbt : τ b = 2) (haz : τ a = 0) :
    HEq ((normalizedTensorTriangleData A X Y c τ).linearBoundary I a b k)
      ((normalizedTensorTrianglePinched A X Y c τ).toSimplexData.linearBoundary I a b k) := by
  have hx := (normalizedTensorTrianglePinched_obj_zero A X Y c τ a haz).symm
  have hy := (normalizedTensorTrianglePinched_obj_two A X Y c τ b hbt).symm
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.linearBoundary
  rw [← Finset.sum_coe_sort (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b),
    ← Finset.sum_coe_sort (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b)]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sum_heq_of_obj_eq hx hy
  intro j
  have hh := normalizedTensorTriangleData_homOrZero_pinched A X Y c τ
    (I.erase j.val) a b (k + 1) hbt haz
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.smul_sub_heq_of_obj_eq hx hy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j.val) _ 0 _ 0 hh
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq hx hy rfl)
  simpa only [sub_zero] using hs

end SerrePositivity.EInfinity.ComplexLimits
