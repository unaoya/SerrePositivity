module

public import SerrePositivity.FieldTheory.PExponent
public import SerrePositivity.FieldTheory.FrobeniusTowerBasis

/-! # 指数 p^n 未満の単項式基底

桁の基底を、商・余りの同値によって有限台指数の基底へ付け替える。
-/

@[expose] public section
namespace SerrePositivity

namespace PExponent

/-- 境界の等式による添字の同一視。有限台関数そのものは変えない。 -/
def boundEquiv {ι : Type*} {q r : ℕ} (h : q = r) : PExponent q ι ≃ PExponent r ι :=
  Equiv.subtypeEquivProp (by rw [h])

@[simp] theorem boundEquiv_val {ι : Type*} {q r : ℕ} (h : q = r) (d : PExponent q ι) :
    (boundEquiv h d).val = d.val := rfl

end PExponent

/-- n 桁の有限台 p 指数と、指数 p^n 未満の有限台関数との同値。 -/
noncomputable def frobeniusDigitsEquiv {ι : Type*} (p : ℕ) [NeZero p] :
    (n : ℕ) → FrobeniusDigits p ι n ≃ PExponent (p ^ n) ι
  | 0 =>
    { toFun := fun _ ↦ ⟨0, fun _ ↦ by simp⟩
      invFun := fun _ ↦ PUnit.unit
      left_inv := fun _ ↦ rfl
      right_inv := fun d ↦ by
        apply Subtype.ext
        apply Finsupp.ext
        intro i
        have h := d.property i
        change 0 = d.val i
        simp only [pow_zero] at h
        omega }
  | n + 1 =>
    (Equiv.prodCongr (Equiv.refl _) (frobeniusDigitsEquiv (ι := ι) p n)).trans
      ((PExponent.radixEquiv p (p ^ n)).symm.trans
        (PExponent.boundEquiv (Nat.pow_succ').symm))

/-- 添字の同一視は単項式の値も保つ。 -/
theorem pMonomial_frobeniusDigitsEquiv {ι k : Type*} [CommMonoid k]
    (p : ℕ) [NeZero p] (b : ι → k) (n : ℕ) (d : FrobeniusDigits p ι n) :
    pMonomial b (frobeniusDigitsEquiv (ι := ι) p n d) = frobeniusDigitMonomial b n d := by
  induction n with
  | zero =>
    change (0 : ι →₀ ℕ).prod (fun i m ↦ b i ^ m) = 1
    simp
  | succ n ih =>
    change pMonomial b (PExponent.boundEquiv (Nat.pow_succ').symm
      (PExponent.radixJoin p (p ^ n) (d.1, frobeniusDigitsEquiv (ι := ι) p n d.2))) = _
    change pMonomial b (PExponent.radixJoin p (p ^ n)
      (d.1, frobeniusDigitsEquiv (ι := ι) p n d.2)) = _
    rw [pMonomial_radixJoin, ih]
    rfl

variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
  {ι : Type*} {b : ι → k}

/-- 指数が各成分で p^n 未満の単項式を基底にする。 -/
noncomputable def IsPBasis.frobeniusMonomialBasis (hb : IsPBasis k p b) (n : ℕ) :
    Module.Basis (PExponent (p ^ n) ι) (frobeniusPowerSubfield k p n) k :=
  (hb.frobeniusTowerBasis n).reindex (frobeniusDigitsEquiv (ι := ι) p n)

@[simp] theorem IsPBasis.frobeniusMonomialBasis_apply (hb : IsPBasis k p b) (n : ℕ)
    (d : PExponent (p ^ n) ι) : hb.frobeniusMonomialBasis n d = pMonomial b d := by
  rw [IsPBasis.frobeniusMonomialBasis, Module.Basis.reindex_apply,
    hb.frobeniusTowerBasis_apply, ← pMonomial_frobeniusDigitsEquiv,
    Equiv.apply_symm_apply]

end SerrePositivity
