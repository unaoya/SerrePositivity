module

public import SerrePositivity.FieldTheory.PMonomial

/-! # 有限台指数の桁分解

指数の商と余りはともに有限台。添字集合の有限性は要求しない。
-/

@[expose] public section
namespace SerrePositivity
namespace PExponent

variable {ι : Type*} (p q : ℕ) [NeZero q]

/-- q を基数とした、高い桁と低い桁。 -/
noncomputable def radixSplit (d : PExponent (p * q) ι) : PExponent p ι × PExponent q ι :=
  (⟨d.val.mapRange (fun a ↦ a / q) (Nat.zero_div q), fun i ↦
      (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (NeZero.ne q))).mpr (d.property i)⟩,
    ⟨d.val.mapRange (fun a ↦ a % q) (Nat.zero_mod q), fun _ ↦
      Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q))⟩)

/-- 高い桁に q を掛けて低い桁を加える。 -/
noncomputable def radixJoin (d : PExponent p ι × PExponent q ι) : PExponent (p * q) ι :=
  ⟨d.1.val.mapRange (fun a ↦ a * q) (Nat.zero_mul q) + d.2.val, fun i ↦ by
    change d.1.val i * q + d.2.val i < p * q
    have h₁ := d.1.property i
    have h₂ := d.2.property i
    calc
      d.1.val i * q + d.2.val i < d.1.val i * q + q := Nat.add_lt_add_left h₂ _
      _ = (d.1.val i + 1) * q := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ p * q := Nat.mul_le_mul_right q (by omega)⟩

/-- 商・余りによる有限台指数の同値。 -/
noncomputable def radixEquiv : PExponent (p * q) ι ≃ PExponent p ι × PExponent q ι where
  toFun := radixSplit p q
  invFun := radixJoin p q
  left_inv d := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    change d.val i / q * q + d.val i % q = d.val i
    exact Nat.div_add_mod' _ _
  right_inv d := by
    apply Prod.ext <;> apply Subtype.ext <;> apply Finsupp.ext <;> intro i
    · change (d.1.val i * q + d.2.val i) / q = d.1.val i
      have h := d.2.property i
      rw [Nat.mul_comm (d.1.val i) q,
        Nat.mul_add_div (Nat.pos_of_ne_zero (NeZero.ne q)), Nat.div_eq_of_lt h,
        Nat.add_zero]
    · change (d.1.val i * q + d.2.val i) % q = d.2.val i
      simp [Nat.add_mod, Nat.mod_eq_of_lt (d.2.property i)]

end PExponent

/-- 桁の結合は単項式の積に対応する。標数の仮定は不要。 -/
theorem pMonomial_radixJoin {ι k : Type*} [CommMonoid k] (p q : ℕ) [NeZero q]
    (b : ι → k) (d : PExponent p ι × PExponent q ι) :
    pMonomial b (PExponent.radixJoin p q d) = (pMonomial b d.1) ^ q * pMonomial b d.2 := by
  rw [pMonomial, PExponent.radixJoin,
    Finsupp.prod_add_index' (by intro i; simp) (by intro i a c; exact pow_add _ _ _),
    Finsupp.prod_mapRange_index (by intro i; simp)]
  simp only [pMonomial, pow_mul, Finsupp.prod, Finset.prod_pow]

end SerrePositivity
