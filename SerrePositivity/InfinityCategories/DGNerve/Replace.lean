module
public import SerrePositivity.InfinityCategories.DGNerve.HornPartial

/-! # 一つの部分集合の斉次成分の置換

概要：対象族を固定したまま一つの部分集合の成分を置き換える。
方針：集合の等号で分岐し、その集合に届かない制限では元のデータと一致することを使う。
規約：HA Proposition 1.3.1.10。使われ方：ホーンの欠けた面の成分の補正。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：指定した一集合の成分を新しい射族へ置き換える。
方針：集合の等式を消去して端点と次数の証明をそのまま新しい射族に渡す。
規約：HA Proposition 1.3.1.10。使われ方：既知データから欠けた面の成分を補正する。 -/
@[reducible]
def replace {n : ℕ} (s : SimplexData A D n) (M : Finset (Fin (n + 1)))
    (f : ∀ a b k (hM : 2 ≤ M.card),
      a = M.min' (Index.nonempty hM) → b = M.max' (Index.nonempty hM) →
      k = 2 - (M.card : ℤ) → GradedHom A (s.obj a) (s.obj b) k) : SimplexData A D n where
  obj := s.obj
  hom I a b k hI ha hb hk := by
    by_cases h : I = M
    · subst I
      exact f a b k hI ha hb hk
    · exact s.hom I a b k hI ha hb hk

/-- 概要：置き換えた集合では新しい成分を評価する。
方針：集合の等号の第一分岐を評価する。
規約：HA Proposition 1.3.1.10。使われ方：欠けた面の補正値の計算。 -/
lemma replace_hom_same {n : ℕ} (s : SimplexData A D n) (M : Finset (Fin (n + 1)))
    (f : ∀ a b k (hM : 2 ≤ M.card),
      a = M.min' (Index.nonempty hM) → b = M.max' (Index.nonempty hM) →
      k = 2 - (M.card : ℤ) → GradedHom A (s.obj a) (s.obj b) k)
    (a b : Fin (n + 1)) (k : ℤ) (hM : 2 ≤ M.card)
    (ha : a = M.min' (Index.nonempty hM)) (hb : b = M.max' (Index.nonempty hM))
    (hk : k = 2 - (M.card : ℤ)) :
    (s.replace M f).hom M a b k hM ha hb hk = f a b k hM ha hb hk := by
  simp [replace]

/-- 概要：指定集合以外の成分は置換しても変わらない。
方針：集合の等号の第二分岐を評価する。
規約：HA Proposition 1.3.1.10。使われ方：既知の成分の保存。 -/
lemma replace_hom_of_ne {n : ℕ} (s : SimplexData A D n) (M : Finset (Fin (n + 1)))
    (f : ∀ a b k (hM : 2 ≤ M.card),
      a = M.min' (Index.nonempty hM) → b = M.max' (Index.nonempty hM) →
      k = 2 - (M.card : ℤ) → GradedHom A (s.obj a) (s.obj b) k)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hne : I ≠ M) :
    (s.replace M f).hom I a b k hI ha hb hk = s.hom I a b k hI ha hb hk := by
  simp only [replace, dite_eq_right hne]

/-- 概要：置換した集合に像が届かない引き戻しは元のデータの引き戻しと等しい。
方針：単射分岐の像は指定集合と異なり、非単射分岐は対象族だけで決まる。
規約：HA Proposition 1.3.1.10。使われ方：欠けた面の補正が既知の全ての面を保存すること。 -/
lemma replace_pullback_of_omits {m n : ℕ} (s : SimplexData A D n)
    (M : Finset (Fin (n + 1)))
    (f : ∀ a b k (hM : 2 ≤ M.card),
      a = M.min' (Index.nonempty hM) → b = M.max' (Index.nonempty hM) →
      k = 2 - (M.card : ℤ) → GradedHom A (s.obj a) (s.obj b) k)
    (α : Fin (m + 1) →o Fin (n + 1)) (j : Fin (n + 1)) (hj : j ∈ M)
    (hα : ∀ x, α x ≠ j) :
    (s.replace M f).pullback α = s.pullback α := by
  apply SimplexData.ext
  · rfl
  apply heq_of_eq
  funext J a b k hJ ha hb hk
  by_cases hi : Set.InjOn α (J : Set (Fin (m + 1)))
  · rw [pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi,
      pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
    apply replace_hom_of_ne
    intro h
    have hm : j ∈ J.image α := h.symm ▸ hj
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hm
    exact hα x hx
  · simp only [pullback, dite_eq_right hi]

/-- 概要：集合自身の成分を置き換えても、その集合の各内部点の寄与は変わらない。
方針：削除集合と左右の切断集合はいずれも元の集合の真部分集合であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：欠けた面の補正がその右辺を変えないこと。 -/
lemma term_replace_self {n : ℕ} (s : SimplexData A D n) (I : Finset (Fin (n + 1)))
    (f : ∀ a b k (hI : 2 ≤ I.card),
      a = I.min' (Index.nonempty hI) → b = I.max' (Index.nonempty hI) →
      k = 2 - (I.card : ℤ) → GradedHom A (s.obj a) (s.obj b) k)
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    (s.replace I f).term I a b k hI ha hb hk j hj haj hjb =
      s.term I a b k hI ha hb hk j hj haj hjb := by
  have hE : I.erase j ≠ I := by
    intro h
    exact Finset.notMem_erase j I (h.symm ▸ hj)
  have hL : I.filter (· ≤ j) ≠ I := by
    intro h
    have hm : b ∈ I.filter (· ≤ j) := h.symm ▸ (hb ▸ I.max'_mem _)
    exact not_le_of_gt hjb (Finset.mem_filter.mp hm).2
  have hR : I.filter (j ≤ ·) ≠ I := by
    intro h
    have hm : a ∈ I.filter (j ≤ ·) := h.symm ▸ (ha ▸ I.min'_mem _)
    exact not_le_of_gt haj (Finset.mem_filter.mp hm).2
  simp [term, replace, hE, hL, hR]

/-- 概要：集合自身の成分を置き換えても、その集合の方程式の右辺は変わらない。
方針：右辺の有限和の各内部点の寄与が変わらないことを使う。
規約：HA Proposition 1.3.1.10。使われ方：補正後の欠けた面の方程式を元の右辺で検証する。 -/
lemma rhs_replace_self {n : ℕ} (s : SimplexData A D n) (I : Finset (Fin (n + 1)))
    (f : ∀ a b k (hI : 2 ≤ I.card),
      a = I.min' (Index.nonempty hI) → b = I.max' (Index.nonempty hI) →
      k = 2 - (I.card : ℤ) → GradedHom A (s.obj a) (s.obj b) k)
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (s.replace I f).rhs I a b k hI ha hb hk = s.rhs I a b k hI ha hb hk := by
  unfold rhs
  apply Finset.sum_congr rfl
  intro j _
  by_cases hint : a < j.val ∧ j.val < b
  · simp only [dite_eq_left hint, term_replace_self]
  · simp only [dite_eq_right hint]

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
