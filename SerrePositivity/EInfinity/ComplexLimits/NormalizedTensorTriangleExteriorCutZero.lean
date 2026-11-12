module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleExteriorTerms
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

lemma normalizedTensorTriangleData_cutCompose_zero {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I)
    (haj : a < j) (hjb : j < b) (hbt : τ b = 2) (haz : τ a = 0) (hjz : τ j = 0) :
    HEq ((normalizedTensorTriangleData A X Y c τ).cutCompose I a b k j)
      ((normalizedTensorTrianglePinched A X Y c τ).toSimplexData.cutCompose I a b k j) := by
  let s := normalizedTensorTriangleData A X Y c τ
  let t := (normalizedTensorTrianglePinched A X Y c τ).toSimplexData
  let L := I.filter (· ≤ j)
  let R := I.filter (j ≤ ·)
  have ham : IsLeast (I : Set (Fin (n + 1))) a := by rw [ha]; exact I.isLeast_min' _
  have hbm : IsGreatest (I : Set (Fin (n + 1))) b := by rw [hb]; exact I.isGreatest_max' _
  have hL : 2 ≤ L.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two ham.1 hj haj
  have hR : 2 ≤ R.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj hbm.1 hjb
  have hsum : (2 - (L.card : ℤ)) + (2 - (R.card : ℤ)) = k + 1 := by
    have hsplit : L.card + R.card = I.card + 1 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj
    omega
  have hx := (normalizedTensorTrianglePinched_obj_zero A X Y c τ a haz).symm
  have hy := (normalizedTensorTrianglePinched_obj_two A X Y c τ b hbt).symm
  have hjx := (normalizedTensorTrianglePinched_obj_zero A X Y c τ j hjz).symm
  have hjt : τ j ≠ 2 := by rw [hjz]; decide
  change HEq (s.cutCompose I a b k j) (t.cutCompose I a b k j)
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cutCompose
  dsimp only [L, R] at hsum
  simp only [dite_eq_left hsum]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq s R j b _ hR (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbm hjb.le _) rfl,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq s L a j _ hL (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min ham haj.le _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _) rfl,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq t R j b _ hR (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hj _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbm hjb.le _) rfl,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq t L a j _ hL (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min ham haj.le _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hj _) rfl]
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq hx hjx hy rfl rfl rfl _ _ _ _ ?_ ?_ _ _
  · exact normalizedTensorTriangleData_hom_pinched A X Y c τ _ _ _ _ _ _ _ _ hbt hjz
  · refine (normalizedTensorTriangleData_hom_front A X Y c τ _ _ _ _ _ _ _ _ hjt).trans ?_
    apply normalizedTensorTriangleFront_Pinched_zero_hom A X Y c τ
    intro i hi
    have hij : i ≤ j := (Finset.mem_filter.mp hi).2
    exact le_antisymm (hjz ▸ τ.monotone hij) (Fin.zero_le _)

end SerrePositivity.EInfinity.ComplexLimits
