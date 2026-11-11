module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataComponents
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PullbackEquation

/-! # 単体データの制限の右辺の比較

概要：制限の等式から同じ像の部分集合の方程式の右辺の一致を得る。
方針：右辺の単射による移送の公式にデータの等式を適用する。
規約：HA Construction 1.3.1.6、Proposition 1.3.1.10。使われ方：左右の共通の先頭・D 側右辺の比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：等しい単体データの同じ右辺は異種等号で一致する。
方針：単体データの等式を消去する。
規約：HA Construction 1.3.1.6。使われ方：自然性の単体データの等式を斉次右辺に評価する。 -/
lemma rhs_heq_of_eq {n : ℕ} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n} (hst : s = t)
    (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)) :
    HEq (s.rhs J a b k hJ ha hb hk) (t.rhs J a b k hJ ha hb hk) := by
  subst t
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (rhs_heq_of_eq)


/-- 概要：二つの単射による制限が等しいなら、像の部分集合の右辺は異種等号で一致する。
方針：制限の等式を右辺で評価し、引き戻しの単射分岐を両側で使う。
規約：HA Proposition 1.3.1.10。使われ方：二つのホーン面の重なりの右辺の比較。 -/
lemma rhs_heq_of_pullback_eq {l m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D m) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (α : Fin (l + 1) →o Fin (m + 1)) (β : Fin (l + 1) →o Fin (n + 1))
    (h : s.pullback α = t.pullback β)
    (J : Finset (Fin (l + 1))) (a b : Fin (l + 1)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ))
    (hα : Set.InjOn α (J : Set (Fin (l + 1))))
    (hβ : Set.InjOn β (J : Set (Fin (l + 1)))) :
    HEq (s.rhs (J.image α) (α a) (α b) k (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hα hJ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone (by rw [ha]; exact J.isLeast_min' _) _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone (by rw [hb]; exact J.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injOn hα]; exact hk))
      (t.rhs (J.image β) (β a) (β b) k (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hβ hJ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min β.monotone (by rw [ha]; exact J.isLeast_min' _) _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max β.monotone (by rw [hb]; exact J.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injOn hβ]; exact hk)) := by
  have hh := rhs_heq_of_eq h J a b k hJ ha hb hk
  change HEq ((s.pullback α).rhs J a b k hJ ha hb hk)
    ((t.pullback β).rhs J a b k hJ ha hb hk) at hh
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullback_rhs_of_inj _ _ _ _ _ _ _ _ _ _ hα,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullback_rhs_of_inj _ _ _ _ _ _ _ _ _ _ hβ] at hh
  exact hh

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (rhs_heq_of_pullback_eq)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
