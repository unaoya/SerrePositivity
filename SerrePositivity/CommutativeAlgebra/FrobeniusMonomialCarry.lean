module

public import SerrePositivity.FieldTheory.PMonomialSpan
public import SerrePositivity.FieldTheory.FrobeniusPowerSubfield

/-! # 指定持ち上げの単項式の繰り上がり

各生成元の p^n 乗関係から、単項式の積の係数を実際に計算する。
持ち上げ先に標数・局所性・有限性を仮定しない。
-/

@[expose] public section
namespace SerrePositivity

variable {k A ι : Type*} [Field k] [CommRing A] {p : ℕ} [Fact p.Prime] [CharP k p]
  (n : ℕ) (b : ι → k) (β : ι → A) (c : frobeniusPowerSubfield k p n →+* A)
  (hβ : ∀ i, β i ^ p ^ n = c (frobeniusPowerEquiv k p n (b i)))

include hβ

/-- 生成元の冪関係は、すべての有限台単項式の冪関係を与える。 -/
theorem map_frobenius_finsuppMonomial (d : ι →₀ ℕ) :
    c (frobeniusPowerEquiv k p n (d.prod (fun i m ↦ b i ^ m))) =
      (d.prod (fun i m ↦ β i ^ m)) ^ p ^ n := by
  rw [map_finsuppProd, map_finsuppProd]
  simp only [map_pow, ← hβ, Finsupp.prod, ← Finset.prod_pow, ← pow_mul]
  apply Finset.prod_congr rfl
  intro i _
  rw [Nat.mul_comm]

/-- 指数の和を p^n で割り、繰り上がりを係数写像の値へ移す。 -/
theorem pMonomial_mul_frobeniusCarry (d e : PExponent (p ^ n) ι) :
    pMonomial β d * pMonomial β e =
      c (frobeniusPowerEquiv k p n
        ((d.val + e.val).prod (fun i m ↦ b i ^ (m / p ^ n)))) *
          pMonomial β (PExponent.remainder (p ^ n) (d.val + e.val)) := by
  have hc := map_frobenius_finsuppMonomial n b β c hβ
    ((d.val + e.val).mapRange (fun m ↦ m / p ^ n) (Nat.zero_div _))
  rw [Finsupp.prod_mapRange_index (fun i ↦ pow_zero (b i)),
    Finsupp.prod_mapRange_index (fun i ↦ pow_zero (β i))] at hc
  rw [hc]
  rw [pMonomial, pMonomial,
    ← Finsupp.prod_add_index' (by intro i; simp) (by intro i a m; exact pow_add _ _ _)]
  exact finsuppMonomial_eq_pow_mul_remainder (p ^ n) β (d.val + e.val)

end SerrePositivity
