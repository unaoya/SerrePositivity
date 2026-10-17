module
public import SerrePositivity.InfinityCategories.DGNerve.DataComponents
public import SerrePositivity.InfinityCategories.DGNerve.TripleHom

/-! # 単体データの辺・三点成分の引き戻しによる比較

概要：単射の制限が指定データと等しいなら、辺と三点成分を異種等号で比較できる。
方針：二点・三点集合の像を計算し、一般の成分の制限の等式を評価する。
規約：HA Construction 1.3.1.6、Example 1.3.1.8。使われ方：標準 fiber の錐の各成分の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：単射による制限の等式から対応する辺の成分は異種等号で一致する。
方針：二点集合の成分で等式を評価し、像が両端の二点集合になることを使う。
規約：HA Example 1.3.1.8。使われ方：回収した脚の cochain を指定された chain map と比較する。 -/
lemma edgeHom_heq_of_pullback_eq {m n : ℕ} (s : SimplexData A D n) (t : SimplexData A D m)
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α) (h : s.pullback α = t)
    (a b : Fin (m + 1)) (hab : a < b) (hab' : α a < α b) :
    HEq (s.edgeHom (α a) (α b) hab') (t.edgeHom a b hab) := by
  have hJ : 2 ≤ ({a, b} : Finset (Fin (m + 1))).card := by simp [ne_of_lt hab]
  have ha : a = ({a, b} : Finset (Fin (m + 1))).min' (Index.nonempty hJ) := by
    symm
    exact (Finset.min'_eq_iff _ _ _).2 (by simp [hab.le])
  have hb : b = ({a, b} : Finset (Fin (m + 1))).max' (Index.nonempty hJ) := by
    symm
    exact (Finset.max'_eq_iff _ _ _).2 (by simp [hab.le])
  have hk : (0 : ℤ) = 2 - (({a, b} : Finset (Fin (m + 1))).card : ℤ) := by simp [ne_of_lt hab]
  have H := hom_heq_of_eq h {a, b} a b 0 hJ ha hb hk
  rw [pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hα.injOn] at H
  simpa only [edgeHom, Finset.image_insert, Finset.image_singleton] using H

/-- 概要：単射による制限の等式から対応する三点成分は異種等号で一致する。
方針：三点集合の成分で等式を評価し、像が対応する三点集合になることを使う。
規約：HA Example 1.3.1.8。使われ方：回収したホモトピーを指定された次数 −1 の成分と比較する。 -/
lemma tripleHom_heq_of_pullback_eq {m n : ℕ} (s : SimplexData A D n) (t : SimplexData A D m)
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α) (h : s.pullback α = t)
    (a b c : Fin (m + 1)) (hab : a < b) (hbc : b < c)
    (hab' : α a < α b) (hbc' : α b < α c) :
    HEq (s.tripleHom (α a) (α b) (α c) hab' hbc') (t.tripleHom a b c hab hbc) := by
  have hJ : 2 ≤ ({a, b, c} : Finset (Fin (m + 1))).card := by
    simp [ne_of_lt hab, ne_of_lt hbc, ne_of_lt (hab.trans hbc)]
  have ha : a = ({a, b, c} : Finset (Fin (m + 1))).min' (Index.nonempty hJ) := by
    symm
    exact (Finset.min'_eq_iff _ _ _).2 (by simp [hab.le, (hab.trans hbc).le])
  have hc : c = ({a, b, c} : Finset (Fin (m + 1))).max' (Index.nonempty hJ) := by
    symm
    exact (Finset.max'_eq_iff _ _ _).2 (by simp [hbc.le, (hab.trans hbc).le])
  have hk : (-1 : ℤ) = 2 - (({a, b, c} : Finset (Fin (m + 1))).card : ℤ) := by
    simp [ne_of_lt hab, ne_of_lt hbc, ne_of_lt (hab.trans hbc)]
  have H := hom_heq_of_eq h {a, b, c} a c (-1) hJ ha hc hk
  rw [pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hα.injOn] at H
  simpa only [tripleHom, Finset.image_insert, Finset.image_singleton] using H

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
