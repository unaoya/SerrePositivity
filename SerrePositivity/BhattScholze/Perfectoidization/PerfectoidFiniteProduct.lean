module

public import SerrePositivity.BhattScholze.Inputs.Perfectoidization
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectoidRingEquiv
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationIdentity
public import Mathlib.RingTheory.Finiteness.Basic

/-! # Finite products from the existing universal integral-perfectoidization input

Coordinate maps to the original perfectoid ring give a retraction of the
chosen universal object. Universality makes this a two-sided inverse. This
proof explicitly retains the existing B-I existence dependency.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze

/-- A finite product of copies of a perfectoid ring is perfectoid, including the
empty product. This proof uses the existing integral-existence input B-I. -/
theorem isIntegralPerfectoid_finPi
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (r : ℕ) : IsIntegralPerfectoid (Fin r → R) p := by
  obtain ⟨C, hC, f, hf⟩ := Inputs.exists_perfectoidization_of_integral R (Fin r → R) p hR
  let := hC
  let k : C →+* (Fin r → R) :=
    RingHom.pi fun i => hf.lift hR (Pi.evalRingHom (fun _ : Fin r => R) i)
  have hkf : k.comp f = RingHom.id (Fin r → R) := by
    apply RingHom.ext
    intro x
    apply funext
    intro i
    exact RingHom.congr_fun (hf.lift_comp hR (Pi.evalRingHom (fun _ : Fin r => R) i)) x
  have hfk : f.comp k = RingHom.id C := by
    obtain ⟨l, _hl, hu⟩ := hf.2 C hf.1 f
    exact (hu (f.comp k) (by
      change (f.comp k).comp f = f
      rw [RingHom.comp_assoc, hkf, RingHom.comp_id])).trans
      (hu (RingHom.id C) (RingHom.id_comp f)).symm
  let e : (Fin r → R) ≃+* C :=
    { f with invFun := k
             left_inv := fun x => RingHom.congr_fun hkf x
             right_inv := fun x => RingHom.congr_fun hfk x }
  exact isIntegralPerfectoid_of_ringEquiv p e.symm hf.1

/-- Any specified universal perfectoidization of the finite product is its
original unit as an algebra equivalence over the original base. -/
theorem finiteProduct_perfectoidization_exists_algEquiv
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (r : ℕ)
    (C : Type u) [CommRing C] [Algebra R C]
    (f : (Fin r → R) →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) :
    ∃ e : (Fin r → R) ≃ₐ[R] C, e.toAlgHom = f := by
  obtain ⟨e, he⟩ := (isIntegralPerfectoid_finPi R p hR r).isPerfectoidization_id.exists_equiv p hf
  have hef : e.toRingHom = f.toRingHom := by simpa only [RingHom.comp_id] using he
  let e' : (Fin r → R) ≃ₐ[R] C := AlgEquiv.ofRingEquiv (f := e) fun s => by
    change e.toRingHom (algebraMap R (Fin r → R) s) = algebraMap R C s
    rw [hef]
    exact f.commutes s
  exact ⟨e', by ext x; exact RingHom.congr_fun hef x⟩

end SerrePositivity.BhattScholze
