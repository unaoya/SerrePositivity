module
public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Localization.Integral

/-! # Algebraically closed residue fields of absolutely integrally closed rings

The finite étale fiber comparison is an actual algebra equivalence. It supplies
fiber data for the local almost comparison; no global trivialization is asserted.
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity
open Polynomial
open scoped TensorProduct

/-- Absolute integral closedness descends through every surjective ring map. -/
theorem IsAbsolutelyIntegrallyClosed.of_surjective
    {R S : Type u} [CommRing R] [CommRing S] (hR : IsAbsolutelyIntegrallyClosed R)
    (f : R →+* S) (hf : Function.Surjective f) : IsAbsolutelyIntegrallyClosed S := by
  intro P hP hdeg
  obtain ⟨Q, hQ, hdegree, hmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective hf P) hP
  obtain ⟨x, hx⟩ := hR Q hmonic (hdegree ▸ hdeg)
  refine ⟨f x, ?_⟩
  change P.eval (f x) = 0
  rw [← hQ, Polynomial.eval_map]
  rw [Polynomial.eval₂_at_apply]
  rw [hx, map_zero]

theorem IsAbsolutelyIntegrallyClosed.quotient
    {R : Type u} [CommRing R] (hR : IsAbsolutelyIntegrallyClosed R) (I : Ideal R) :
    IsAbsolutelyIntegrallyClosed (R ⧸ I) :=
  hR.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- Absolute integral closedness persists under arbitrary localization, including
localization at a zero divisor. Monic lifting is applied after clearing denominators. -/
theorem IsAbsolutelyIntegrallyClosed.localization
    {R : Type u} [CommRing R] (hR : IsAbsolutelyIntegrallyClosed R)
    (M : Submonoid R) (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S] :
    IsAbsolutelyIntegrallyClosed S := by
  intro P hP hdeg
  let s := IsLocalization.commonDenom M P.support P.coeff
  have hl : P.scaleRoots (algebraMap R S s) ∈ Polynomial.lifts (algebraMap R S) := by
    apply IsLocalization.scaleRoots_commonDenom_mem_lifts M P
    rw [hP.leadingCoeff]
    exact one_mem _
  obtain ⟨Q, hQ, hdegree, hmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl
    ((Polynomial.monic_scaleRoots_iff _).mpr hP)
  obtain ⟨x, hx⟩ := hR Q hmonic (by simpa only [hdegree, Polynomial.natDegree_scaleRoots] using hdeg)
  have hscaled : (P.scaleRoots (algebraMap R S s)).eval (algebraMap R S x) = 0 := by
    rw [← hQ, Polynomial.eval_map_apply, hx, map_zero]
  obtain ⟨u, hu⟩ := IsLocalization.map_units S s
  let y : S := ↑u⁻¹ * algebraMap R S x
  have hmul : algebraMap R S s * y = algebraMap R S x := by
    rw [← hu]
    simp [y]
  have he := P.scaleRoots_eval_mul y (algebraMap R S s)
  rw [hmul, hscaled] at he
  refine ⟨y, ?_⟩
  exact ((IsLocalization.map_units S s).pow P.natDegree).mul_right_eq_zero.mp he.symm

/-- On a field the monic-root condition implies the standard algebraic closedness class. -/
theorem IsAbsolutelyIntegrallyClosed.isAlgClosed
    {K : Type u} [Field K] (hK : IsAbsolutelyIntegrallyClosed K) : IsAlgClosed K := by
  apply IsAlgClosed.of_exists_root
  intro P hP hirr
  exact hK P hP hirr.natDegree_pos

/-- Every maximal residue field of the original ring is algebraically closed. -/
theorem IsAbsolutelyIntegrallyClosed.residue_isAlgClosed
    {R : Type u} [CommRing R] (hR : IsAbsolutelyIntegrallyClosed R)
    (m : Ideal R) [m.IsMaximal] :
    letI := Ideal.Quotient.field m
    IsAlgClosed (R ⧸ m) := by
  letI := Ideal.Quotient.field m
  exact (hR.quotient m).isAlgClosed

/-- A finite étale fiber over a maximal residue field splits into a finite product
of that same residue field, including the rank-zero algebra. -/
theorem IsAbsolutelyIntegrallyClosed.finiteEtale_residueFiber_exists_algEquiv
    {R : Type u} [CommRing R] (hR : IsAbsolutelyIntegrallyClosed R)
    (m : Ideal R) [m.IsMaximal]
    (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A] :
    letI := Ideal.Quotient.field m
    ∃ r : ℕ, Nonempty ((R ⧸ m) ⊗[R] A ≃ₐ[R ⧸ m] (Fin r → R ⧸ m)) := by
  letI := Ideal.Quotient.field m
  letI := hR.residue_isAlgClosed m
  let K := R ⧸ m
  let B := K ⊗[R] A
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed K B
  letI : IsArtinianRing B := isArtinian_of_tower K inferInstance
  letI := Fintype.ofFinite (PrimeSpectrum B)
  exact ⟨Fintype.card (PrimeSpectrum B),
    ⟨e.trans (AlgEquiv.piCongrLeft' K (fun _ : PrimeSpectrum B => K)
      (Fintype.equivFin (PrimeSpectrum B)))⟩⟩

end SerrePositivity
