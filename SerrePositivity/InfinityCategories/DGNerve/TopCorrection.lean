module
public import SerrePositivity.InfinityCategories.DGNerve.EquationTransfer
public import SerrePositivity.InfinityCategories.DGNerve.HornEquation

/-! # 最上位方程式の一成分による補正

概要：内部点を削除した成分の置換が、最上位方程式の右辺をどう変えるか計算する。
方針：端点を保つ削除集合はどの切断集合とも異なり、削除項だけが変わることを使う。
規約：HA Proposition 1.3.1.10。使われ方：欠けた面の値を入れて最上位方程式を解く。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：二つの内部点が異なるなら、一方の削除成分の置換は他方の寄与を変えない。
方針：削除集合の相違と、端点を両方含む集合と片側切断との相違を使う。
規約：HA Proposition 1.3.1.10。使われ方：最上位方程式の補正で変わらない項の消去。 -/
lemma term_replace_of_ne {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (i : Fin (n + 1)) (hi : i ∈ I) (hai : a < i) (hib : i < b)
    (f : ∀ c d q (hM : 2 ≤ (I.erase i).card),
      c = (I.erase i).min' (Index.nonempty hM) →
      d = (I.erase i).max' (Index.nonempty hM) →
      q = 2 - ((I.erase i).card : ℤ) → GradedHom A (s.obj c) (s.obj d) q)
    (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) (hji : j ≠ i) :
    (s.replace (I.erase i) f).term I a b k hI ha hb hk j hj haj hjb =
      s.term I a b k hI ha hb hk j hj haj hjb := by
  have ham : a ∈ I := ha ▸ I.min'_mem _
  have hbm : b ∈ I := hb ▸ I.max'_mem _
  have hE : I.erase j ≠ I.erase i := by
    intro h
    have hm : i ∈ I.erase j := Finset.mem_erase.mpr ⟨hji.symm, hi⟩
    rw [h] at hm
    exact Finset.notMem_erase i I hm
  have hL : I.filter (· ≤ j) ≠ I.erase i := by
    intro h
    have hm : b ∈ I.filter (· ≤ j) := h.symm ▸ Finset.mem_erase.mpr ⟨ne_of_gt hib, hbm⟩
    exact not_le_of_gt hjb (Finset.mem_filter.mp hm).2
  have hR : I.filter (j ≤ ·) ≠ I.erase i := by
    intro h
    have hm : a ∈ I.filter (j ≤ ·) := h.symm ▸ Finset.mem_erase.mpr ⟨ne_of_lt hai, ham⟩
    exact not_le_of_gt haj (Finset.mem_filter.mp hm).2
  simp [term, replace, hE, hL, hR]

/-- 概要：指定した内部点の寄与の変化は、削除成分の変化にその点の符号を掛けたもの。
方針：二つの切断成分は変わらないことを使い、符号付きの差を整理する。
規約：HA Proposition 1.3.1.10。使われ方：最上位方程式の右辺の補正量。 -/
lemma term_replace_same {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (i : Fin (n + 1)) (hi : i ∈ I) (hai : a < i) (hib : i < b)
    (f : ∀ c d q (hM : 2 ≤ (I.erase i).card),
      c = (I.erase i).min' (Index.nonempty hM) →
      d = (I.erase i).max' (Index.nonempty hM) →
      q = 2 - ((I.erase i).card : ℤ) → GradedHom A (s.obj c) (s.obj d) q) :
    ((s.replace (I.erase i) f).term I a b k hI ha hb hk i hi hai hib :
      GradedHom A (s.obj a) (s.obj b) (k + 1)) -
      s.term I a b k hI ha hb hk i hi hai hib =
    Index.sign I i •
      (f a b (k + 1) (Index.erase_two (ha ▸ I.min'_mem _) (hb ▸ I.max'_mem _) hai hib)
        (Index.erase_min (by rw [ha]; exact I.isLeast_min' _) hai _)
        (Index.erase_max (by rw [hb]; exact I.isGreatest_max' _) hib _)
        (by have := Finset.card_erase_add_one hi; omega) -
      s.hom (I.erase i) a b (k + 1)
        (Index.erase_two (ha ▸ I.min'_mem _) (hb ▸ I.max'_mem _) hai hib)
        (Index.erase_min (by rw [ha]; exact I.isLeast_min' _) hai _)
        (Index.erase_max (by rw [hb]; exact I.isGreatest_max' _) hib _)
        (by have := Finset.card_erase_add_one hi; omega)) := by
  have ham : a ∈ I := ha ▸ I.min'_mem _
  have hbm : b ∈ I := hb ▸ I.max'_mem _
  have hL : I.filter (· ≤ i) ≠ I.erase i := by
    intro h
    have hm : b ∈ I.filter (· ≤ i) := h.symm ▸ Finset.mem_erase.mpr ⟨ne_of_gt hib, hbm⟩
    exact not_le_of_gt hib (Finset.mem_filter.mp hm).2
  have hR : I.filter (i ≤ ·) ≠ I.erase i := by
    intro h
    have hm : a ∈ I.filter (i ≤ ·) := h.symm ▸ Finset.mem_erase.mpr ⟨ne_of_lt hai, ham⟩
    exact not_le_of_gt hai (Finset.mem_filter.mp hm).2
  simp only [term, replace, hL, hR, ↓reduceDIte, Index.sign]
  simp only [← smul_sub]
  congr 1
  abel

/-- 概要：削除成分の置換による右辺の変化は、その成分の変化に内部点の符号を掛けたもの。
方針：有限和の差を取り、指定点以外の寄与が変わらないことから一項だけを残す。
規約：HA Proposition 1.3.1.10。使われ方：最上位方程式の右辺を零にする補正の計算。 -/
lemma rhs_replace {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (i : Fin (n + 1)) (hi : i ∈ I) (hai : a < i) (hib : i < b)
    (f : ∀ c d q (hM : 2 ≤ (I.erase i).card),
      c = (I.erase i).min' (Index.nonempty hM) →
      d = (I.erase i).max' (Index.nonempty hM) →
      q = 2 - ((I.erase i).card : ℤ) → GradedHom A (s.obj c) (s.obj d) q) :
    ((s.replace (I.erase i) f).rhs I a b k hI ha hb hk :
      GradedHom A (s.obj a) (s.obj b) (k + 1)) -
      s.rhs I a b k hI ha hb hk =
    Index.sign I i •
      (f a b (k + 1) (Index.erase_two (ha ▸ I.min'_mem _) (hb ▸ I.max'_mem _) hai hib)
        (Index.erase_min (by rw [ha]; exact I.isLeast_min' _) hai _)
        (Index.erase_max (by rw [hb]; exact I.isGreatest_max' _) hib _)
        (by have := Finset.card_erase_add_one hi; omega) -
      s.hom (I.erase i) a b (k + 1)
        (Index.erase_two (ha ▸ I.min'_mem _) (hb ▸ I.max'_mem _) hai hib)
        (Index.erase_min (by rw [ha]; exact I.isLeast_min' _) hai _)
        (Index.erase_max (by rw [hb]; exact I.isGreatest_max' _) hib _)
        (by have := Finset.card_erase_add_one hi; omega)) := by
  unfold rhs
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single (⟨i, hi⟩ : I)]
  · simp only [dite_eq_left (show a < i ∧ i < b from ⟨hai, hib⟩)]
    exact term_replace_same s I a b k hI ha hb hk i hi hai hib f
  · intro j _ hji
    by_cases hjint : a < j.val ∧ j.val < b
    · simp only [dite_eq_left hjint]
      rw [term_replace_of_ne s I a b k hI ha hb hk i hi hai hib f j.val j.property
        hjint.1 hjint.2 (fun he => hji (Subtype.ext he))]
      exact sub_self _
    · simp only [dite_eq_right hjint, sub_self]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

/-- 概要：最上位方程式の残る右辺を、内部点を削除した成分の値で打ち消す射族。
方針：欠けた面の端点と次数を元の集合の端点と一つ上の次数に同定し、符号付き右辺を引く。
規約：HA Proposition 1.3.1.10。使われ方：最上位成分を零にしたホーン充填候補の補正値。 -/
def correctingHom {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (i : Fin (n + 1)) (hi : i ∈ I) (hai : a < i) (hib : i < b) :
    ∀ c d q (hM : 2 ≤ (I.erase i).card),
      c = (I.erase i).min' (Index.nonempty hM) →
      d = (I.erase i).max' (Index.nonempty hM) →
      q = 2 - ((I.erase i).card : ℤ) → GradedHom A (s.obj c) (s.obj d) q := by
  intro c d q hM hc hd hq
  have hac : c = a := hc.trans (Index.erase_min (by rw [ha]; exact I.isLeast_min' _) hai _).symm
  have hbd : d = b := hd.trans (Index.erase_max (by rw [hb]; exact I.isGreatest_max' _) hib _).symm
  have hqk : q = k + 1 := by have := Finset.card_erase_add_one hi; omega
  exact cast (by rw [hac, hbd, hqk])
    (s.hom (I.erase i) a b (k + 1) hM
      (Index.erase_min (by rw [ha]; exact I.isLeast_min' _) hai _)
      (Index.erase_max (by rw [hb]; exact I.isGreatest_max' _) hib _)
      (by have := Finset.card_erase_add_one hi; omega) -
      Index.sign I i • s.rhs I a b k hI ha hb hk)

/-- 概要：補正射族を元の端点と一つ上の次数で評価すると、元の削除成分から符号付き右辺を引く。
方針：端点と次数の同定が反射律になることを使う。
規約：HA Proposition 1.3.1.10。使われ方：最上位方程式の補正量の簡約。 -/
lemma correctingHom_self {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (i : Fin (n + 1)) (hi : i ∈ I) (hai : a < i) (hib : i < b)
    (hM : 2 ≤ (I.erase i).card)
    (haM : a = (I.erase i).min' (Index.nonempty hM))
    (hbM : b = (I.erase i).max' (Index.nonempty hM))
    (hkM : k + 1 = 2 - ((I.erase i).card : ℤ)) :
    s.correctingHom I a b k hI ha hb hk i hi hai hib a b (k + 1) hM haM hbM hkM =
      s.hom (I.erase i) a b (k + 1) hM haM hbM hkM -
        Index.sign I i • s.rhs I a b k hI ha hb hk := by
  rfl

/-- 概要：一つの内部削除成分を補正した単体データ。
方針：最上位の右辺を打ち消す射族で、一つの成分だけを置換する。
規約：HA Proposition 1.3.1.10。使われ方：ホーン充填候補。欠けた面自身の方程式は別途必要。 -/
def solveTop {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (i : Fin (n + 1)) (hi : i ∈ I) (hai : a < i) (hib : i < b) :
    SimplexData A D n :=
  s.replace (I.erase i) (s.correctingHom I a b k hI ha hb hk i hi hai hib)

/-- 概要：補正したデータでは、指定した集合の方程式の右辺は零となる。
方針：右辺の変化は負の元の右辺に等しく、負一冪を二度掛けると一になることを使う。
規約：HA Proposition 1.3.1.10。使われ方：最上位成分を零とする充填の方程式。 -/
lemma rhs_solveTop {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (i : Fin (n + 1)) (hi : i ∈ I) (hai : a < i) (hib : i < b) :
    (s.solveTop I a b k hI ha hb hk i hi hai hib).rhs I a b k hI ha hb hk = 0 := by
  have hh := rhs_replace s I a b k hI ha hb hk i hi hai hib
    (s.correctingHom I a b k hI ha hb hk i hi hai hib)
  rw [correctingHom_self] at hh
  simp only [sub_sub_cancel_left, smul_neg] at hh
  have hs : Index.sign I i • (Index.sign I i • s.rhs I a b k hI ha hb hk) =
      s.rhs I a b k hI ha hb hk := by simp [Index.sign, smul_smul]
  rw [hs] at hh
  exact (sub_eq_iff_eq_add.mp hh).trans (neg_add_cancel _)

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
