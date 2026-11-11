module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EquationTransfer
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornEquation

/-! # 最上位方程式の一成分による補正

概要：内部点を削除した成分の置換が、最上位方程式の右辺をどう変えるか計算する。
方針：端点を保つ削除集合はどの切断集合とも異なり、削除項だけが変わることを使う。
規約：HA Proposition 1.3.1.10。使われ方：欠けた面の値を入れて最上位方程式を解く。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：二つの内部点が異なるなら、一方の削除成分の置換は他方の寄与を変えない。
方針：削除集合の相違と、端点を両方含む集合と片側切断との相違を使う。
規約：HA Proposition 1.3.1.10。使われ方：最上位方程式の補正で変わらない項の消去。 -/
lemma term_replace_of_ne {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (i : Fin (n + 1)) (hi : i ∈ I) (hai : a < i) (hib : i < b)
    (f : ∀ c d q (hM : 2 ≤ (I.erase i).card),
      c = (I.erase i).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      d = (I.erase i).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
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
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace, hE, hL, hR]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (term_replace_of_ne)


/-- 概要：指定した内部点の寄与の変化は、削除成分の変化にその点の符号を掛けたもの。
方針：二つの切断成分は変わらないことを使い、符号付きの差を整理する。
規約：HA Proposition 1.3.1.10。使われ方：最上位方程式の右辺の補正量。 -/
lemma term_replace_same {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (i : Fin (n + 1)) (hi : i ∈ I) (hai : a < i) (hib : i < b)
    (f : ∀ c d q (hM : 2 ≤ (I.erase i).card),
      c = (I.erase i).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      d = (I.erase i).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      q = 2 - ((I.erase i).card : ℤ) → GradedHom A (s.obj c) (s.obj d) q) :
    ((s.replace (I.erase i) f).term I a b k hI ha hb hk i hi hai hib :
      GradedHom A (s.obj a) (s.obj b) (k + 1)) -
      s.term I a b k hI ha hb hk i hi hai hib =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I i •
      (f a b (k + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_two (ha ▸ I.min'_mem _) (hb ▸ I.max'_mem _) hai hib)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_min (by rw [ha]; exact I.isLeast_min' _) hai _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_max (by rw [hb]; exact I.isGreatest_max' _) hib _)
        (by have := Finset.card_erase_add_one hi; omega) -
      s.hom (I.erase i) a b (k + 1)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_two (ha ▸ I.min'_mem _) (hb ▸ I.max'_mem _) hai hib)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_min (by rw [ha]; exact I.isLeast_min' _) hai _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_max (by rw [hb]; exact I.isGreatest_max' _) hib _)
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
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace, hL, hR, ↓reduceDIte, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign]
  simp only [← smul_sub]
  congr 1
  abel

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (term_replace_same)


/-- 概要：削除成分の置換による右辺の変化は、その成分の変化に内部点の符号を掛けたもの。
方針：有限和の差を取り、指定点以外の寄与が変わらないことから一項だけを残す。
規約：HA Proposition 1.3.1.10。使われ方：最上位方程式の右辺を零にする補正の計算。 -/
lemma rhs_replace {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (i : Fin (n + 1)) (hi : i ∈ I) (hai : a < i) (hib : i < b)
    (f : ∀ c d q (hM : 2 ≤ (I.erase i).card),
      c = (I.erase i).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      d = (I.erase i).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      q = 2 - ((I.erase i).card : ℤ) → GradedHom A (s.obj c) (s.obj d) q) :
    ((s.replace (I.erase i) f).rhs I a b k hI ha hb hk :
      GradedHom A (s.obj a) (s.obj b) (k + 1)) -
      s.rhs I a b k hI ha hb hk =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I i •
      (f a b (k + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_two (ha ▸ I.min'_mem _) (hb ▸ I.max'_mem _) hai hib)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_min (by rw [ha]; exact I.isLeast_min' _) hai _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_max (by rw [hb]; exact I.isGreatest_max' _) hib _)
        (by have := Finset.card_erase_add_one hi; omega) -
      s.hom (I.erase i) a b (k + 1)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_two (ha ▸ I.min'_mem _) (hb ▸ I.max'_mem _) hai hib)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_min (by rw [ha]; exact I.isLeast_min' _) hai _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_max (by rw [hb]; exact I.isGreatest_max' _) hib _)
        (by have := Finset.card_erase_add_one hi; omega)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
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

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (rhs_replace)


/-- 概要：最上位方程式の残る右辺を、内部点を削除した成分の値で打ち消す射族。
方針：欠けた面の端点と次数を元の集合の端点と一つ上の次数に同定し、符号付き右辺を引く。
規約：HA Proposition 1.3.1.10。使われ方：最上位成分を零にしたホーン充填候補の補正値。 -/
def correctingHom {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (i : Fin (n + 1)) (hi : i ∈ I) (hai : a < i) (hib : i < b) :
    ∀ c d q (hM : 2 ≤ (I.erase i).card),
      c = (I.erase i).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      d = (I.erase i).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      q = 2 - ((I.erase i).card : ℤ) → GradedHom A (s.obj c) (s.obj d) q := by
  intro c d q hM hc hd hq
  have hac : c = a := hc.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_min (by rw [ha]; exact I.isLeast_min' _) hai _).symm
  have hbd : d = b := hd.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_max (by rw [hb]; exact I.isGreatest_max' _) hib _).symm
  have hqk : q = k + 1 := by have := Finset.card_erase_add_one hi; omega
  exact cast (by rw [hac, hbd, hqk])
    (s.hom (I.erase i) a b (k + 1) hM
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_min (by rw [ha]; exact I.isLeast_min' _) hai _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_max (by rw [hb]; exact I.isGreatest_max' _) hib _)
      (by have := Finset.card_erase_add_one hi; omega) -
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I i • s.rhs I a b k hI ha hb hk)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (correctingHom)


/-- 概要：補正射族を元の端点と一つ上の次数で評価すると、元の削除成分から符号付き右辺を引く。
方針：端点と次数の同定が反射律になることを使う。
規約：HA Proposition 1.3.1.10。使われ方：最上位方程式の補正量の簡約。 -/
lemma correctingHom_self {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (i : Fin (n + 1)) (hi : i ∈ I) (hai : a < i) (hib : i < b)
    (hM : 2 ≤ (I.erase i).card)
    (haM : a = (I.erase i).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM))
    (hbM : b = (I.erase i).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM))
    (hkM : k + 1 = 2 - ((I.erase i).card : ℤ)) :
    s.correctingHom I a b k hI ha hb hk i hi hai hib a b (k + 1) hM haM hbM hkM =
      s.hom (I.erase i) a b (k + 1) hM haM hbM hkM -
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I i • s.rhs I a b k hI ha hb hk := by
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (correctingHom_self)


/-- 概要：一つの内部削除成分を補正した単体データ。
方針：最上位の右辺を打ち消す射族で、一つの成分だけを置換する。
規約：HA Proposition 1.3.1.10。使われ方：ホーン充填候補。欠けた面自身の方程式は別途必要。 -/
def solveTop {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (i : Fin (n + 1)) (hi : i ∈ I) (hai : a < i) (hib : i < b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n :=
  s.replace (I.erase i) (s.correctingHom I a b k hI ha hb hk i hi hai hib)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (solveTop)


/-- 概要：補正したデータでは、指定した集合の方程式の右辺は零となる。
方針：右辺の変化は負の元の右辺に等しく、負一冪を二度掛けると一になることを使う。
規約：HA Proposition 1.3.1.10。使われ方：最上位成分を零とする充填の方程式。 -/
lemma rhs_solveTop {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (i : Fin (n + 1)) (hi : i ∈ I) (hai : a < i) (hib : i < b) :
    (s.solveTop I a b k hI ha hb hk i hi hai hib).rhs I a b k hI ha hb hk = 0 := by
  have hh := rhs_replace s I a b k hI ha hb hk i hi hai hib
    (s.correctingHom I a b k hI ha hb hk i hi hai hib)
  rw [correctingHom_self] at hh
  simp only [sub_sub_cancel_left, smul_neg] at hh
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I i • (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I i • s.rhs I a b k hI ha hb hk) =
      s.rhs I a b k hI ha hb hk := by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign, smul_smul]
  rw [hs] at hh
  exact (sub_eq_iff_eq_add.mp hh).trans (neg_add_cancel _)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (rhs_solveTop)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
