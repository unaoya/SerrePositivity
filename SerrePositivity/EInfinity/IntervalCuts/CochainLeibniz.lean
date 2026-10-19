module

public import SerrePositivity.EInfinity.IntervalCuts.CochainDegrees

/-!
# 区間余演算の全整数 Leibniz 則

概要：Berger–Fresse §2.2.7 の区間切断微分等式を全整数の双線形演算へまとめる。
方針：区間の二つの非零次数と χ の非正次数に分け、線形恒等式を移す。
規約：右入力の微分項は第一入力次数の Koszul 符号を持つ。
使われ方：区間切断余演算を実際の複体射へ束ねる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：等しい整数次数で証明した微分条件を次数の和へ移す（BF §2.2.7）。
方針：次の入力次数と出力次数の変数を等式で消去する。
規約：元の入力次数とその元は固定する。
使われ方：自然数の負号での線形等式を Leibniz 則の文言へ直す。 -/
lemma cochainActionBilinear_d_reindex (n : ℕ) (r s r' s' t t' : ℤ)
    (hr : r' = r + 1) (hs : s' = s + 1) (ht : t = r + s) (ht' : t' = r + s + 1)
    (x : (Surjection.complex A n).X r) (y : (interval A).X s)
    (H : (power (interval A) n).d t t'
        (cochainActionBilinear A n r s t (by omega) x y) =
      cochainActionBilinear A n r' s t' (by omega)
        ((Surjection.complex A n).d r r' x) y +
      r.negOnePow • cochainActionBilinear A n r s' t' (by omega) x
        ((interval A).d s s' y)) :
    (power (interval A) n).d (r + s) (r + s + 1)
        (cochainActionBilinear A n r s (r + s) rfl x y) =
      cochainActionBilinear A n (r + 1) s (r + s + 1) (by omega)
        ((Surjection.complex A n).d r (r + 1) x) y +
      r.negOnePow • cochainActionBilinear A n r (s + 1) (r + s + 1) (by omega) x
        ((interval A).d s (s + 1) y) := by
  subst r'
  subst s'
  subst t
  subst t'
  exact H

/-- 概要：区間余演算の全整数双線形成分は Leibniz 則を満たす（BF §2.2.7）。
方針：正次数と区間の零成分を除き、頂点・辺の線形微分等式を使う。
規約：全 arity、任意の可換環と実際の複体の元。
使われ方：tensorLift に渡す微分条件。 -/
lemma cochainActionBilinear_d (n : ℕ) (r s : ℤ)
    (x : (Surjection.complex A n).X r) (y : (interval A).X s) :
    (power (interval A) n).d (r + s) (r + s + 1)
        (cochainActionBilinear A n r s (r + s) rfl x y) =
      cochainActionBilinear A n (r + 1) s (r + s + 1) (by omega)
        ((Surjection.complex A n).d r (r + 1) x) y +
      r.negOnePow • cochainActionBilinear A n r (s + 1) (r + s + 1) (by omega) x
        ((interval A).d s (s + 1) y) := by
  by_cases hr : 0 < r
  · rw [Surjection.complex_eq_zero_of_positive A n r hr x]
    simp
  have hr : r ≤ 0 := by omega
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, r = -(d : ℤ) := ⟨(-r).toNat, by omega⟩
  by_cases hs : s = 0
  · subst s
    cases d with
    | zero =>
      apply cochainActionBilinear_d_reindex A n _ _ 1 1 0 1
        (by omega) (by omega) (by omega) (by omega) x y
      rw [cochainActionBilinear_eq_zero_of_positive A n 1 0 1 (by omega) (by omega),
        cochainActionBilinear_eq_zero_of_other A n _ 1 1 (by omega) (by omega) (by omega)]
      simp only [LinearMap.zero_apply, smul_zero, zero_add]
      exact congrArg (fun f : (interval A).X 0 →ₗ[A] (power (interval A) n).X 1 => f y)
        (vertexInputBilinear_d_eq_zero A n 0 ((Surjection.complexXIso A n 0).hom x))
    | succ d =>
      apply cochainActionBilinear_d_reindex A n _ _ (-(d : ℤ)) 1
        (-((d + 1 : ℕ) : ℤ)) (-(d : ℤ))
        (by omega) (by omega) (by omega) (by omega) x y
      rw [cochainActionBilinear_eq_zero_of_other A n _ 1 _ (by omega) (by omega) (by omega)]
      simp only [LinearMap.zero_apply, smul_zero, add_zero,
        cochainActionBilinear_neg_vertex, surjection_d_neg_apply,
        vertexInputBilinear_differential]
      rw [vertexInputBilinear_eq_zero_of_positive A n (d + 1) (by omega)]
      change ((power (interval A) n).d (-((d + 1 : ℕ) : ℤ)) (-(d : ℤ))).hom 0 = 0
      exact map_zero _
  by_cases hs1 : s = -1
  · subst s
    cases d with
    | zero =>
      apply cochainActionBilinear_d_reindex A n _ _ 1 0 (-1) 0
        (by omega) (by omega) (by omega) (by omega) x y
      rw [cochainActionBilinear_eq_zero_of_positive A n 1 (-1) 0 (by omega) (by omega)]
      simp only [LinearMap.zero_apply, zero_add, Nat.cast_zero, neg_zero,
        Int.negOnePow_zero, one_smul]
      exact congrArg (fun f : (interval A).X (-1) →ₗ[A]
        (power (interval A) n).X 0 => f y)
        (edgeInputBilinear_d_zero A n ((Surjection.complexXIso A n 0).hom x))
    | succ d =>
      apply cochainActionBilinear_d_reindex A n _ _ (-(d : ℤ)) 0
        (-((d + 2 : ℕ) : ℤ)) (-((d + 1 : ℕ) : ℤ))
        (by omega) (by omega) (by omega) (by omega) x y
      rw [cochainActionBilinear_neg_vertex,
        vertexInputBilinear_eq_zero_of_positive A n (d + 1) (by omega)]
      simp only [LinearMap.zero_apply, smul_zero, add_zero,
        cochainActionBilinear_neg_edge, surjection_d_neg_apply]
      exact congrArg (fun f : (interval A).X (-1) →ₗ[A]
        (power (interval A) n).X (-((d + 1 : ℕ) : ℤ)) => f y)
        (edgeInputBilinear_d_positive A n d
          ((Surjection.complexXIso A n (d + 1)).hom x))
  · rw [interval_eq_zero_of_other A s hs hs1 y]
    simp

end SerrePositivity.EInfinity.IntervalCuts
