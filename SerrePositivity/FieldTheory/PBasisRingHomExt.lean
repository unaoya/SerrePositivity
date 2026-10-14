module

public import SerrePositivity.FieldTheory.PBasis

/-! # p-basis と Frobenius 冪による環写像の一致

p-basis の有限台展開を使い、係数の p 乗での一致から写像全体の一致を導く。
-/

@[expose] public section
namespace SerrePositivity

variable {k A : Type*} [Field k] [CommRing A]
variable {p : ℕ} [Fact p.Prime] [CharP k p]
variable {ι : Type*} {b : ι → k}

/-- p-basis と全ての p 乗で一致する環写像は一致する。 -/
theorem IsPBasis.ringHom_ext_of_eq_pow (hb : IsPBasis k p b)
    (l₁ l₂ : k →+* A) (hbmap : ∀ i, l₁ (b i) = l₂ (b i))
    (hpow : ∀ x, l₁ (x ^ p) = l₂ (x ^ p)) : l₁ = l₂ := by
  classical
  have hmono (d : PExponent p ι) : l₁ (pMonomial b d) = l₂ (pMonomial b d) := by
    simp only [pMonomial, Finsupp.prod, map_prod, map_pow, hbmap]
  ext x
  rw [← hb.sum_expansionEquiv x]
  simp only [Finsupp.sum, map_sum, map_mul, hpow, hmono]

/-- p-basis と、一つの Frobenius 冪の像で一致すれば、写像全体が一致する。 -/
theorem IsPBasis.ringHom_ext_of_eq_pow_exp (hb : IsPBasis k p b)
    (l₁ l₂ : k →+* A) (hbmap : ∀ i, l₁ (b i) = l₂ (b i))
    (n : ℕ) (hpow : ∀ x, l₁ (x ^ p ^ n) = l₂ (x ^ p ^ n)) : l₁ = l₂ := by
  induction n with
  | zero =>
    ext x
    simpa using hpow x
  | succ n ih =>
    let m₁ := l₁.comp (iterateFrobenius k p n)
    let m₂ := l₂.comp (iterateFrobenius k p n)
    have hm : m₁ = m₂ := by
      apply hb.ringHom_ext_of_eq_pow
      · intro i
        change l₁ ((b i) ^ p ^ n) = l₂ ((b i) ^ p ^ n)
        simp only [map_pow, hbmap]
      · intro x
        change l₁ ((x ^ p) ^ p ^ n) = l₂ ((x ^ p) ^ p ^ n)
        simpa only [← pow_mul, Nat.pow_succ, Nat.mul_comm] using hpow x
    apply ih
    intro x
    exact RingHom.congr_fun hm x

end SerrePositivity
