module

public import Mathlib.RingTheory.WittVector.TeichmullerSeries
public import Mathlib.LinearAlgebra.SModEq.Pow

/-! # 完全標数p環からのWitt持上げの一意性 -/

@[expose] public noncomputable section
namespace SerrePositivity
variable {p : ℕ} [Fact p.Prime] {k A : Type*} [CommRing k] [CharP k p]
    [PerfectRing k p] [CommRing A]

/-- 同じmod p写像を持つWitt写像はTeichmüller元で一致する。 -/
theorem wittLift_teichmuller_eq [IsHausdorff (Ideal.span {(p : A)}) A]
    (f g : WittVector p k →+* A)
    (h : (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp f =
      (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp g) (x : k) :
    f (WittVector.teichmuller p x) = g (WittVector.teichmuller p x) := by
  apply (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : A)})).mpr
  intro n
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have hsurj : Function.Surjective (fun y : k ↦ y ^ p ^ n) := by
    have hs := (PerfectRing.bijective_frobenius (R := k) (p := p)).surjective.iterate n
    change Function.Surjective (frobenius k p)^[n] at hs
    intro a
    obtain ⟨y, hy⟩ := hs a
    exact ⟨y, by simpa only [iterate_frobenius] using hy⟩
  obtain ⟨y, rfl⟩ := hsurj x
  have hmod : f (WittVector.teichmuller p y) ≡ g (WittVector.teichmuller p y)
      [SMOD Ideal.span {(p : A)}] := by
    exact SModEq.idealQuotientMk.mpr (RingHom.congr_fun h _)
  have he := hmod.pow_pow_add_one
    (Ideal.mem_span_singleton_self (p : A)) n
  have ht := he.mono (Ideal.pow_le_pow_right (Nat.le_succ n))
  simpa only [map_pow] using ht

/-- 同じmod p写像を持つ任意の二つの環準同型は一致する。連続性を仮定しない。 -/
theorem wittLift_unique [IsHausdorff (Ideal.span {(p : A)}) A]
    (f g : WittVector p k →+* A)
    (h : (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp f =
      (Ideal.Quotient.mk (Ideal.span {(p : A)})).comp g) : f = g := by
  ext x
  apply (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : A)})).mpr
  intro n
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  apply SModEq.idealQuotientMk.mpr
  have he : (Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ n)).comp f =
      (Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ n)).comp g := by
    apply WittVector.eq_of_apply_teichmuller_eq
    · refine ⟨n, ?_⟩
      rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self (p : A)) n)
    · intro y
      simp only [RingHom.comp_apply, wittLift_teichmuller_eq f g h y]
  exact RingHom.congr_fun he x

end SerrePositivity
