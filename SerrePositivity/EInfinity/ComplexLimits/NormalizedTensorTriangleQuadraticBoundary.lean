module
public import SerrePositivity.EInfinity.ComplexLimits.SimplexDataFilteredSum
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleExteriorCutZero
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleExteriorCutTwo
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleMiddleEquality

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

lemma normalizedTensorTriangleData_quadraticBoundary_pinched {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (hI : 2 ≤ I.card) (hc : 3 ≤ I.card) (a b : Fin (n + 1)) (k : ℤ)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (haz : τ a = 0) (hbt : τ b = 2) :
    HEq ((normalizedTensorTriangleData A X Y c τ).quadraticBoundary I a b k)
      ((normalizedTensorTrianglePinched A X Y c τ).toSimplexData.quadraticBoundary I a b k) := by
  have hx := (normalizedTensorTrianglePinched_obj_zero A X Y c τ a haz).symm
  have hy := (normalizedTensorTrianglePinched_obj_two A X Y c τ b hbt).symm
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.quadraticBoundary
  apply gradedHom_sum_heq_of_filter hx hy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b) (fun j => τ j = 1)
  · exact normalizedTensorTriangle_middle_sum_heq A X Y c τ I hI hc a b k ha hb hk haz hbt
  · intro j hj hn
    have hjI := (Finset.mem_filter.mp hj).1
    have haj := (Finset.mem_filter.mp hj).2.1
    have hjb := (Finset.mem_filter.mp hj).2.2
    have hcut : HEq ((normalizedTensorTriangleData A X Y c τ).cutCompose I a b k j)
        ((normalizedTensorTrianglePinched A X Y c τ).toSimplexData.cutCompose I a b k j) := by
      by_cases hj0 : τ j = 0
      · exact normalizedTensorTriangleData_cutCompose_zero A X Y c τ I a b k hI ha hb hk
          j hjI haj hjb hbt haz hj0
      · have hj2 : τ j = 2 := by omega
        exact normalizedTensorTriangleData_cutCompose_two A X Y c τ I a b k hI ha hb hk
          j hjI haj hjb hbt haz hj2
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.smul_sub_heq_of_obj_eq hx hy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j) _ 0 _ 0 hcut
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq hx hy rfl)
    simpa only [sub_zero] using he

end SerrePositivity.EInfinity.ComplexLimits
