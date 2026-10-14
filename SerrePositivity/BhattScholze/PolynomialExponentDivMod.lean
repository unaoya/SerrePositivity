module

public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Tactic

/-! # B4-6：多項式の指数の商と余り

各変数の指数をnで割り、n未満の有限台指数と商指数に分解する。
多項式のexpand射の加群基底を構成するためのBS専用計算。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze

/-- 各指数がn未満の有限台指数。 -/
abbrev PolynomialExponentRemainder (n : ℕ) (σ : Type u) :=
  {d : σ →₀ ℕ // ∀ s, d s < n}

/-- 有限台指数の各座標の商と余りによる同値。任意個の変数を含む。 -/
def polynomialExponentDivModEquiv (n : ℕ) (σ : Type u) (hn : 0 < n) :
    (σ →₀ ℕ) ≃ PolynomialExponentRemainder n σ × (σ →₀ ℕ) where
  toFun d := (⟨d.mapRange (fun k ↦ k % n) (Nat.zero_mod n),
    fun s ↦ by simpa using Nat.mod_lt (d s) hn⟩,
    d.mapRange (fun k ↦ k / n) (Nat.zero_div n))
  invFun x := n • x.2 + x.1.val
  left_inv d := by
    ext s
    simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul]
    exact Nat.div_add_mod (d s) n
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      ext s
      simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul]
      simp [Nat.add_mod, Nat.mod_eq_of_lt (x.1.property s)]
    · ext s
      simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul]
      rw [Nat.mul_add_div hn, Nat.div_eq_of_lt (x.1.property s), add_zero]

/-- 商・余りから元の指数を復元する式。 -/
@[simp] theorem polynomialExponentDivModEquiv_symm_apply
    (n : ℕ) (σ : Type u) (hn : 0 < n)
    (b : PolynomialExponentRemainder n σ) (q : σ →₀ ℕ) :
    (polynomialExponentDivModEquiv n σ hn).symm (b, q) = n • q + b.val := rfl

end SerrePositivity.BhattScholze
