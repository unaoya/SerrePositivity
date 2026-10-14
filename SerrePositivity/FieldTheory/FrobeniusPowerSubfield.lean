module

public import SerrePositivity.FieldTheory.PBasis

/-! # 高い Frobenius 冪の係数部分体

体全体とその p^n 乗部分体の同型を使う。体が完全であることは要求しない。
-/

@[expose] public section
namespace SerrePositivity

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- p^n 乗の像の部分体。 -/
def frobeniusPowerSubfield (n : ℕ) : Subfield k := (iterateFrobenius k p n).fieldRange

@[simp] theorem mem_frobeniusPowerSubfield (n : ℕ) (x : k) :
    x ∈ frobeniusPowerSubfield k p n ↔ ∃ y : k, y ^ p ^ n = x := Iff.rfl

/-- Frobenius 冪は体とその像部分体との同型。 -/
noncomputable def frobeniusPowerEquiv (n : ℕ) : k ≃+* frobeniusPowerSubfield k p n :=
  (iterateFrobenius k p n).rangeRestrictFieldEquiv

@[simp] theorem frobeniusPowerEquiv_apply_coe (n : ℕ) (x : k) :
    (frobeniusPowerEquiv k p n x : k) = x ^ p ^ n := rfl

@[simp] theorem frobeniusPowerSubfield_zero : frobeniusPowerSubfield k p 0 = ⊤ := by
  ext x
  simp

@[simp] theorem frobeniusPowerSubfield_one : frobeniusPowerSubfield k p 1 = pPowerSubfield k p := by
  ext x
  simp

end SerrePositivity
