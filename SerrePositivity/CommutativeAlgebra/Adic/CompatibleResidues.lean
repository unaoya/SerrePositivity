module

public import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# 完備環の隣接する剰余の逆極限

## 概要
完備環の元は、隣接段で両立するイデアル冪剰余の列と一対一に対応する。

## 方針
剰余の代表元を取り、Cauchy 列の完備性と Hausdorff 性を使う。

## 規約
添字は自然数。遷移は通常の商射。

## 使われ方
完備 Čech 複体の各次数を有限剰余の逆極限で計算する。
-/

public noncomputable section

namespace SerrePositivity

variable {R : Type*} [CommRing R]

/-- 概要：完備環のイデアル冪剰余の隣接逆塔は元を一意に復元する。
方針：全ての遷移との両立は隣接段の両立から従うので、代表元は Cauchy 列になる。
規約：分離性も含む古典的な `IsAdicComplete`。
使われ方：BS 著者版 Corollary 3.12 の完備 Čech の次数ごとの比較。 -/
theorem existsUnique_of_compatible_idealResidues (I : Ideal R) [IsAdicComplete I R]
    (a : ∀ n : ℕ, R ⧸ I ^ n)
    (ha : ∀ n, Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ) (a (n + 1)) = a n) :
    ∃! x : R, ∀ n, Ideal.Quotient.mk (I ^ n) x = a n := by
  have hpow (n : ℕ) : (I ^ n • ⊤ : Submodule R R) = I ^ n := by
    change (I ^ n • ⊤ : Ideal R) = _
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  choose y hy using fun n ↦ Ideal.Quotient.mk_surjective (a n)
  have hc : ∀ {m n : ℕ}, m ≤ n → y m ≡ y n [SMOD (I ^ m • ⊤ : Submodule R R)] := by
    intro m n h
    rw [hpow, SModEq]
    change Ideal.Quotient.mk (I ^ m) (y m) = Ideal.Quotient.mk (I ^ m) (y n)
    rw [hy, ← Ideal.Quotient.factor_mk (Ideal.pow_le_pow_right h) (y n), hy]
    exact Ideal.Quotient.eq_factor_of_eq_factor_succ
      (fun _ _ le ↦ Ideal.pow_le_pow_right le) a (fun k ↦ (ha k).symm) h
  obtain ⟨x, hx⟩ := IsPrecomplete.prec' (I := I) y hc
  have hq (n : ℕ) : Ideal.Quotient.mk (I ^ n) x = a n := by
    have hn := hx n
    rw [hpow, SModEq] at hn
    exact hn.symm.trans (hy n)
  refine ⟨x, hq, fun z hz ↦ ?_⟩
  apply (AdicCompletion.of_bijective (I := I) (M := R)).injective
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, hz, hq]

end SerrePositivity
