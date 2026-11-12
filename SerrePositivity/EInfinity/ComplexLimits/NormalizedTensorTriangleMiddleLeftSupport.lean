module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTrianglePinchedFrontZero
public import SerrePositivity.EInfinity.ComplexLimits.ConeSecond

/-!
概要：中央相の元の pinched 切断合成は左切断が二点の場合以外で零になる。
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

lemma normalizedTensorTrianglePinched_cutCompose_middle_zero {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (a b j : Fin (n + 1)) (k : ℤ) (hj1 : τ j = 1)
    (hc : (I.filter (· ≤ j)).card ≠ 2) :
    (normalizedTensorTrianglePinched A X Y c τ).toSimplexData.cutCompose I a b k j = 0 := by
  have hj2 : τ j ≠ 2 := by rw [hj1]; decide
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cutCompose
  split_ifs
  · rw [normalizedTensorTrianglePinched_homOrZero_front_zero A X Y c τ _ a j _ hj2 (by omega)]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero _ _
  · rfl

lemma normalizedTensorTrianglePinched_cutCompose_middle_ne_second {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (a b j : Fin (n + 1)) (k : ℤ) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hj : j ∈ I) (haj : a < j) (hj1 : τ j = 1)
    (hne : j ≠ ConeHeadIndex.second I hI) :
    (normalizedTensorTrianglePinched A X Y c τ).toSimplexData.cutCompose I a b k j = 0 := by
  apply normalizedTensorTrianglePinched_cutCompose_middle_zero A X Y c τ I a b j k hj1
  intro hc
  exact hne ((ConeHeadIndex.left_card_two_iff_second I hI j hj
    (by rw [← ha]; exact haj)).mp hc)
end SerrePositivity.EInfinity.ComplexLimits
