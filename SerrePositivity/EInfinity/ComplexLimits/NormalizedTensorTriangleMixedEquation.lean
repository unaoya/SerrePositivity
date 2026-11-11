module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleQuadraticBoundary
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleMixedLinear

/-!
概要：元の全切断和・線形境界の比較から、実三相データの全 HA を証明する。
方針：元の零・中央・二相の全成分を比較し、同じ実単体の方程式を戻す。
規約：面・退化自然性と大域的な接合は別工程。使われ方：大域評価三角形。
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

lemma normalizedTensorTriangleData_equation_mixed {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hc : 3 ≤ I.card) (a b : Fin (n + 1)) (k : ℤ)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (haz : τ a = 0) (hbt : τ b = 2) :
    differential A ((normalizedTensorTriangleData A X Y c τ).hom I a b k hI ha hb hk) =
      (normalizedTensorTriangleData A X Y c τ).rhs I a b k hI ha hb hk := by
  let s := normalizedTensorTriangleData A X Y c τ
  let t := normalizedTensorTrianglePinched A X Y c τ
  have hx := (normalizedTensorTrianglePinched_obj_zero A X Y c τ a haz).symm
  have hy := (normalizedTensorTrianglePinched_obj_two A X Y c τ b hbt).symm
  have hh := normalizedTensorTriangleData_hom_pinched A X Y c τ I a b k hI ha hb hk hbt haz
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq hx hy rfl _ _ hh
  have hl := normalizedTensorTriangleData_linearBoundary_pinched A X Y c τ I a b k hbt haz
  have hq := normalizedTensorTriangleData_quadraticBoundary_pinched A X Y c τ I hI hc
    a b k ha hb hk haz hbt
  have hr : HEq (s.rhs I a b k hI ha hb hk) (t.toSimplexData.rhs I a b k hI ha hb hk) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_eq_linear_sub_quadratic, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_eq_linear_sub_quadratic]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_sub_heq hx hy rfl _ _ _ _ hl hq
  exact eq_of_heq (hd.trans ((heq_of_eq (t.equation I a b k hI ha hb hk)).trans hr.symm))

end SerrePositivity.EInfinity.ComplexLimits
