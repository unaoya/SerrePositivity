module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.Algebra.CharP.Quotient

/-! # 全射の核の正の冪商

商から終域への写像、冪零核、標数の継承と商間の両立を共通化する。
零回目の冪商は用いず、正の冪だけを扱う。
-/

@[expose] public section
namespace SerrePositivity

variable {A B : Type*} [CommRing A] [CommRing B]

/-- 核の正の冪による商から、元の写像の終域への写像。 -/
def kernelPowerQuotientMap (f : A →+* B) (n : ℕ) : A ⧸ (RingHom.ker f) ^ (n + 1) →+* B :=
  Ideal.Quotient.lift _ f ((RingHom.ker f).pow_le_self (Nat.succ_ne_zero n))

@[simp] theorem kernelPowerQuotientMap_mk (f : A →+* B) (n : ℕ) (x : A) :
    kernelPowerQuotientMap f n (Ideal.Quotient.mk ((RingHom.ker f) ^ (n + 1)) x) = f x := rfl

theorem kernelPowerQuotientMap_surjective (f : A →+* B) (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (kernelPowerQuotientMap f n) := by
  intro b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

/-- 商の写像の核の `n + 1` 乗は零。 -/
theorem kernelPowerQuotientMap_ker_pow_eq_bot (f : A →+* B) (n : ℕ) :
    RingHom.ker (kernelPowerQuotientMap f n) ^ (n + 1) = ⊥ := by
  rw [kernelPowerQuotientMap, Ideal.ker_quotient_lift, ← Ideal.map_pow,
    Ideal.map_quotient_self]

/-- 商の写像の核はイデアルとして冪零。各元の冪零性だけではない。 -/
theorem kernelPowerQuotientMap_nilpotent_kernel (f : A →+* B) (n : ℕ) :
    IsNilpotent (RingHom.ker (kernelPowerQuotientMap f n)) :=
  ⟨n + 1, kernelPowerQuotientMap_ker_pow_eq_bot f n⟩

/-- 源と終域の標数が一致すれば、正の冪商にも同じ標数が入る。 -/
theorem kernelPowerQuotient_charP (f : A →+* B) (p n : ℕ) [CharP A p] [CharP B p] :
    CharP (A ⧸ (RingHom.ker f) ^ (n + 1)) p :=
  CharP.quotient' p _ (fun a ha ↦ by
    have h : f (a : A) = 0 := (RingHom.ker f).pow_le_self (Nat.succ_ne_zero n) ha
    rw [map_natCast] at h
    exact (CharP.cast_eq_zero_iff A p a).mpr ((CharP.cast_eq_zero_iff B p a).mp h))

theorem kernelPowerQuotientMap_comp_factorPowSucc (f : A →+* B) (n : ℕ) :
    (kernelPowerQuotientMap f n).comp (Ideal.Quotient.factorPowSucc (RingHom.ker f) (n + 1)) =
      kernelPowerQuotientMap f (n + 1) := by
  ext x
  simp

end SerrePositivity
