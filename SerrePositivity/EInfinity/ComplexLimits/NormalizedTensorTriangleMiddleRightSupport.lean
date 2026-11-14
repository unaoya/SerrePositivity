module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleMixedLinear
public import SerrePositivity.EInfinity.ComplexLimits.ConePenultimate

/-!
概要：中央相の実切断合成は右切断が二点の場合以外で零になる。
方針：元の実 cochain・次数・部分集合と切断の一意性を使う。
規約：残る一項同士の比較は別工程。使われ方：大域評価三角形の混合 HA。
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

lemma normalizedTensorTriangleBack_hom_of_ne {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hk0 : k ≠ 0) :
    (normalizedTensorTriangleBack A X Y c τ).hom I a b k hI ha hb hk = 0 := by
  unfold normalizedTensorTriangleBack
  rw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveSimplex_pullback]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_of_ne _ k hk0

lemma normalizedTensorTriangleData_homOrZero_back_zero {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hbt : τ b = 2) (haz : τ a ≠ 0) (hk0 : k ≠ 0) :
    (normalizedTensorTriangleData A X Y c τ).homOrZero I a b k = 0 := by
  have hbz : τ b ≠ 0 := by rw [hbt]; decide
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero
  split_ifs with hI ha hb hk
  · have hh := normalizedTensorTriangleData_hom_back A X Y c τ I a b k hI ha hb hk hbt haz
    have hz := normalizedTensorTriangleBack_hom_of_ne A X Y c τ I a b k hI ha hb hk hk0
    exact eq_of_heq (hh.trans ((heq_of_eq hz).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (normalizedTensorTriangleBack_obj A X Y c τ a haz)
        (normalizedTensorTriangleBack_obj A X Y c τ b hbz) rfl)))
  all_goals rfl

lemma normalizedTensorTriangleData_cutCompose_middle_zero {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (a b j : Fin (n + 1)) (k : ℤ) (hbt : τ b = 2) (hj1 : τ j = 1)
    (hc : (I.filter (j ≤ ·)).card ≠ 2) :
    (normalizedTensorTriangleData A X Y c τ).cutCompose I a b k j = 0 := by
  have hj0 : τ j ≠ 0 := by rw [hj1]; decide
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cutCompose
  split_ifs
  · rw [normalizedTensorTriangleData_homOrZero_back_zero A X Y c τ _ j b _ hbt hj0
      (by omega)]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose _ _
  · rfl

lemma normalizedTensorTriangleData_cutCompose_middle_ne_penultimate {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (a b j : Fin (n + 1)) (k : ℤ) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hj : j ∈ I) (hjb : j < b) (hbt : τ b = 2) (hj1 : τ j = 1)
    (hne : j ≠ ConeHeadIndex.penultimate I hI) :
    (normalizedTensorTriangleData A X Y c τ).cutCompose I a b k j = 0 := by
  apply normalizedTensorTriangleData_cutCompose_middle_zero A X Y c τ I a b j k hbt hj1
  intro hc
  exact hne ((ConeHeadIndex.right_card_two_iff_penultimate I hI j hj
    (by rw [← hb]; exact hjb)).mp hc)
end SerrePositivity.EInfinity.ComplexLimits
