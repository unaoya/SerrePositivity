module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleCochainDifferential

/-!
# 全整数次数の shuffle の微分条件

概要：Berger–Fresse §1.1.3 の shuffle の Leibniz 則を全整数コチェイン次数で述べる。
方針：正次数の零成分を除き、非正次数を自然数の負号として分類する。
規約：微分は +1、第二の微分項には第一の整数次数の Koszul 符号を付ける。
使われ方：shuffle の成分族をテンソル複体からの chain map にまとめる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory

variable (A : Type u) [CommRing A]

/-- 概要：等しい整数次数で証明した微分条件を標準の次数の和へ移す（Berger–Fresse §1.1.3）。
方針：入力の次の次数と出力次数の変数を等式で消去する。
規約：元の入力次数 r,s とその元は固定する。
使われ方：自然数の負号で書いた微分公式を全整数次数の文言へ直す。 -/
lemma cochainShuffleBilinear_d_reindex (m n : ℕ) (i : Fin (m + 1))
    (r s r' s' t t' : ℤ) (hr : r' = r + 1) (hs : s' = s + 1)
    (ht : t = r + s) (ht' : t' = r + s + 1)
    (x : (complex A (m + 1)).X r) (y : (complex A n).X s)
    (H : (complex A (m + n)).d t t'
        (cochainShuffleBilinear A m n i r s t (by omega) x y) =
      cochainShuffleBilinear A m n i r' s t' (by omega)
        ((complex A (m + 1)).d r r' x) y +
      r.negOnePow • cochainShuffleBilinear A m n i r s' t' (by omega) x
        ((complex A n).d s s' y)) :
    (complex A (m + n)).d (r + s) (r + s + 1)
        (cochainShuffleBilinear A m n i r s (r + s) rfl x y) =
      cochainShuffleBilinear A m n i (r + 1) s (r + s + 1) (by omega)
        ((complex A (m + 1)).d r (r + 1) x) y +
      r.negOnePow • cochainShuffleBilinear A m n i r (s + 1) (r + s + 1) (by omega) x
        ((complex A n).d s (s + 1) y) := by
  subst r'
  subst s'
  subst t
  subst t'
  exact H

/-- 概要：全整数次数の shuffle 双線形成分はコチェインの Leibniz 則を満たす（Berger–Fresse §1.1.3）。
方針：正次数の入力を零にし、負次数・次数0の四つの場合を既存の微分公式へ帰着する。
規約：第二の微分項の符号は r.negOnePow である。
使われ方：テンソル成分の微分条件を純粋テンソル上で証明する。 -/
lemma cochainShuffleBilinear_d (m n : ℕ) (i : Fin (m + 1)) (r s : ℤ)
    (x : (complex A (m + 1)).X r) (y : (complex A n).X s) :
    (complex A (m + n)).d (r + s) (r + s + 1)
        (cochainShuffleBilinear A m n i r s (r + s) rfl x y) =
      cochainShuffleBilinear A m n i (r + 1) s (r + s + 1) (by omega)
        ((complex A (m + 1)).d r (r + 1) x) y +
      r.negOnePow • cochainShuffleBilinear A m n i r (s + 1) (r + s + 1) (by omega) x
        ((complex A n).d s (s + 1) y) := by
  by_cases hr : 0 < r
  · have hx := complex_eq_zero_of_positive A (m + 1) r hr x
    simp only [hx, map_zero, LinearMap.zero_apply, smul_zero, zero_add]
  by_cases hs : 0 < s
  · have hy := complex_eq_zero_of_positive A n s hs y
    simp only [hy, map_zero, smul_zero, add_zero]
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, r = -(p : ℤ) := ⟨(-r).toNat, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, s = -(q : ℤ) := ⟨(-s).toNat, by omega⟩
  cases p with
  | zero =>
    cases q with
    | zero =>
      apply cochainShuffleBilinear_d_reindex A m n i _ _ 1 1 0 1
        (by omega) (by omega) (by omega) (by omega) x y
      rw [cochainShuffleBilinear_eq_zero_of_left_pos A m n i 1 _ _ _ (by decide),
        cochainShuffleBilinear_eq_zero_of_right_pos A m n i _ 1 _ _ (by decide)]
      simp only [LinearMap.zero_apply, smul_zero, add_zero]
      exact complex_eq_zero_of_positive A (m + n) 1 (by decide) _
    | succ q =>
      apply cochainShuffleBilinear_d_reindex A m n i _ _ 1 (-(q : ℤ))
        (-((0 + (q + 1) : ℕ) : ℤ)) (-((0 + q : ℕ) : ℤ))
        (by omega) (by omega) (by omega) (by omega) x y
      rw [cochainShuffleBilinear_eq_zero_of_left_pos A m n i 1 _ _ _ (by decide)]
      simp only [LinearMap.zero_apply, zero_add]
      rw [show (-((0 : ℕ) : ℤ)).negOnePow = 1 from by decide, one_smul]
      exact cochainShuffleBilinear_d_leftZero A m n i q x y
  | succ p =>
    cases q with
    | zero =>
      apply cochainShuffleBilinear_d_reindex A m n i _ _ (-(p : ℤ)) 1
        (-((p + 1 + 0 : ℕ) : ℤ)) (-((p + 0 : ℕ) : ℤ))
        (by omega) (by omega) (by omega) (by omega) x y
      rw [cochainShuffleBilinear_eq_zero_of_right_pos A m n i _ 1 _ _ (by decide)]
      simp only [LinearMap.zero_apply, smul_zero, add_zero]
      exact cochainShuffleBilinear_d_rightZero A m n i p x y
    | succ q =>
      apply cochainShuffleBilinear_d_reindex A m n i _ _ (-(p : ℤ)) (-(q : ℤ))
        (-((p + 1 + (q + 1) : ℕ) : ℤ)) (-((p + 1 + q : ℕ) : ℤ))
        (by omega) (by omega) (by omega) (by omega) x y
      exact cochainShuffleBilinear_d_negative A m n i p q x y

end SerrePositivity.EInfinity.BarrattEccles
