module
public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosedHenselian
public import SerrePositivity.CommutativeAlgebra.LocalResidueLinearMap
public import SerrePositivity.CommutativeAlgebra.FiniteAlgebraLocalizationLift
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Actual finite étale splitting over a local absolutely integrally closed base -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open IsLocalRing
open scoped TensorProduct

/-- Lift all coordinates of the original finite étale fiber simultaneously.
The resulting map to a finite product is an actual algebra equivalence. -/
theorem IsAbsolutelyIntegrallyClosed.finiteEtale_local_exists_algEquiv
    {R A : Type u} [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A] (hR : IsAbsolutelyIntegrallyClosed R) :
    ∃ r : ℕ, Nonempty (A ≃ₐ[R] (Fin r → R)) := by
  classical
  let K := ResidueField R
  have hfiber : ∃ r : ℕ, Nonempty (K ⊗[R] A ≃ₐ[K] (Fin r → K)) :=
    hR.finiteEtale_residueFiber_exists_algEquiv (maximalIdeal R) A
  obtain ⟨r, ⟨e⟩⟩ := hfiber
  let point (i : Fin r) : A →ₐ[R] K :=
    (((Pi.evalAlgHom K (fun _ : Fin r => K) i).comp e.toAlgHom).restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A)
  have hlift (i : Fin r) : ∃ l : A →ₐ[R] R,
      (Algebra.ofId R K).comp l = point i := hR.etale_point_lift (point i)
  choose l hl using hlift
  let F : A →ₐ[R] (Fin r → R) := AlgHom.pi l
  let q := TensorProduct.piScalarRight R K K (Fin r)
  have hcomm (z : K ⊗[R] A) : q (F.toLinearMap.lTensor K z) = e z := by
    induction z using TensorProduct.inductionOn with
    | tmul k a =>
      ext i
      have hi := AlgHom.congr_fun (hl i) a
      change residue R (l i a) = e ((1 : K) ⊗ₜ[R] a) i at hi
      change (l i a) • k = e (k ⊗ₜ[R] a) i
      rw [Algebra.smul_def]
      change residue R (l i a) * k = e (k ⊗ₜ[R] a) i
      rw [hi]
      have hk : k ⊗ₜ[R] a = k • ((1 : K) ⊗ₜ[R] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hk, map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_comm _ _
    | add x y hx hy => simp only [map_add, hx, hy]
  have hbij : Function.Bijective (F.toLinearMap.lTensor K) := by
    constructor
    · intro x y hxy
      apply e.injective
      rw [← hcomm, ← hcomm, hxy]
    · intro y
      obtain ⟨x, hx⟩ := e.surjective (q y)
      refine ⟨x, q.injective ?_⟩
      rw [hcomm, hx]
  exact ⟨r, ⟨AlgEquiv.ofBijective F
    (localLinearMap_bijective_of_residue_bijective F.toLinearMap hbij)⟩⟩

/-- Over the original localization at any prime, the actual scalar-extended finite
étale algebra is a finite product of that same local base. -/
theorem IsAbsolutelyIntegrallyClosed.finiteEtale_localized_exists_algEquiv
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A] (hR : IsAbsolutelyIntegrallyClosed R)
    (p : Ideal R) [p.IsPrime] :
    ∃ r : ℕ, Nonempty ((Localization.AtPrime p) ⊗[R] A ≃ₐ[Localization.AtPrime p]
      (Fin r → Localization.AtPrime p)) :=
  (hR.localization p.primeCompl (Localization.AtPrime p)).finiteEtale_local_exists_algEquiv

/-- All coordinates of the actual stalk splitting descend to one principal neighborhood,
as an algebra map with exactly the specified stalk values. Bijectivity on the principal
neighborhood is the subsequent isomorphism-locus step. -/
theorem IsAbsolutelyIntegrallyClosed.finiteEtale_exists_principal_comparison
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A] (hR : IsAbsolutelyIntegrallyClosed R)
    (p : Ideal R) [p.IsPrime] :
    ∃ (r : ℕ) (d : R) (hd : d ∉ p) (ψ : A →ₐ[R] (Fin r → Localization.Away d))
      (e : (Localization.AtPrime p) ⊗[R] A ≃ₐ[Localization.AtPrime p]
        (Fin r → Localization.AtPrime p)),
      ∀ a i, IsLocalization.Away.liftAlgHom d (f := Algebra.ofId R (Localization.AtPrime p))
        (IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p) ⟨d, hd⟩) (ψ a i) =
          e ((1 : Localization.AtPrime p) ⊗ₜ[R] a) i := by
  letI : Module.FinitePresentation R A := Module.FinitePresentation.of_finite_of_finitePresentation R A
  obtain ⟨r, ⟨e⟩⟩ := hR.finiteEtale_localized_exists_algEquiv (A := A) p
  let φ : A →ₐ[R] (Fin r → Localization.AtPrime p) :=
    (e.toAlgHom.restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[R] (Localization.AtPrime p) ⊗[R] A)
  obtain ⟨d, hd, ψ, hψ⟩ := finiteAlgebra_exists_away_lift_pi p.primeCompl
    (Localization.AtPrime p) r φ
  exact ⟨r, d, hd, ψ, e, hψ⟩

end SerrePositivity
