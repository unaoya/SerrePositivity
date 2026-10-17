module
public import SerrePositivity.InfinityCategories.DGNerve.HornComponents

/-! # 単体データの制限の成分の比較

概要：方程式を仮定しない単体データで、制限の等式から斉次成分の一致を得る。
方針：N2 の成分比較の証明をデータの等式に適用する。
規約：HA Construction 1.3.1.6、Proposition 1.3.1.10。使われ方：左右の充填候補の共通面の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open CategoryTheory Opposite DifferentialGraded
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：等しい単体データの同じ成分は異種等号で一致する。
方針：単体データの等式を消去する。
規約：HA Construction 1.3.1.6。使われ方：自然性の単体データの等式を斉次成分に評価する。 -/
lemma hom_heq_of_eq {n : ℕ} {s t : SimplexData A D n} (hst : s = t)
    (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : b = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)) :
    HEq (s.hom J a b k hJ ha hb hk) (t.hom J a b k hJ ha hb hk) := by
  subst t
  rfl

/-- 概要：二つの単射による制限が等しいなら、像の部分集合の成分は異種等号で一致する。
方針：制限の等式を成分で評価し、引き戻しの単射分岐を両側で使う。
規約：HA Proposition 1.3.1.10。使われ方：二つのホーン面の重なりの成分の比較。 -/
lemma hom_heq_of_pullback_eq {l m n : ℕ} (s : SimplexData A D m) (t : SimplexData A D n)
    (α : Fin (l + 1) →o Fin (m + 1)) (β : Fin (l + 1) →o Fin (n + 1))
    (h : s.pullback α = t.pullback β)
    (J : Finset (Fin (l + 1))) (a b : Fin (l + 1)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : b = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ))
    (hα : Set.InjOn α (J : Set (Fin (l + 1))))
    (hβ : Set.InjOn β (J : Set (Fin (l + 1)))) :
    HEq (s.hom (J.image α) (α a) (α b) k (Index.image_two hα hJ)
      (Index.image_min α.monotone (by rw [ha]; exact J.isLeast_min' _) _)
      (Index.image_max α.monotone (by rw [hb]; exact J.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injOn hα]; exact hk))
      (t.hom (J.image β) (β a) (β b) k (Index.image_two hβ hJ)
      (Index.image_min β.monotone (by rw [ha]; exact J.isLeast_min' _) _)
      (Index.image_max β.monotone (by rw [hb]; exact J.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injOn hβ]; exact hk)) := by
  have hh := hom_heq_of_eq h J a b k hJ ha hb hk
  change HEq ((s.pullback α).hom J a b k hJ ha hb hk)
    ((t.pullback β).hom J a b k hJ ha hb hk) at hh
  rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hα,
    SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hβ] at hh
  exact hh

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
