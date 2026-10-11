module

public import SerrePositivity.CommutativeAlgebra.GradedReesSelf
public import SerrePositivity.CommutativeAlgebra.HilbertSamuelPolynomial
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The associated graded presentation as a graded linear surjection

The polynomial presentation of the associated graded ring is identified with
the self associated graded module, with explicit preservation of each degree.
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.HilbertSamuel

open Polynomial IsLocalRing

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Ideal R)
variable {s : ℕ} (z : Fin s → R) (hz : Ideal.span (Set.range z) = I)

/-- The polynomial presentation, viewed as an `R`-linear map into the self
associated graded module. -/
def gradedPresentationMap :
    MvPolynomial (Fin s) (R ⧸ I) →ₗ[R] ReesGraded R I R :=
  ((reesGradedSelfEquiv R I).symm.toLinearMap.restrictScalars R).comp
    ((gradedReesPresentation R I z hz).toLinearMap.restrictScalars R)

/-- The linear presentation is surjective. -/
theorem gradedPresentationMap_surjective : Function.Surjective (gradedPresentationMap R I z hz) :=
  (reesGradedSelfEquiv R I).symm.surjective.comp
    (gradedReesPresentation_surjective R I z hz)

/-- Lifting coefficients to `R` commutes with the two presentation maps. -/
theorem gradedReesPresentation_map (p : MvPolynomial (Fin s) R) :
    gradedReesPresentation R I z hz (MvPolynomial.map (Ideal.Quotient.mk I) p) =
      Ideal.Quotient.mk _ (reesPresentation R I z hz p) := by
  have hcomp : (gradedReesPresentation R I z hz).toRingHom.comp
      (MvPolynomial.map (Ideal.Quotient.mk I)) =
      (Ideal.Quotient.mk _).comp (reesPresentation R I z hz).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [gradedReesPresentation, reesPresentation]
    · intro i
      simp [gradedReesPresentation]
  exact DFunLike.congr_fun hcomp p

private theorem prod_monomial {ι : Type*} (t : Finset ι) (d : ι → ℕ) (a : ι → R) :
    (∏ i ∈ t, monomial (d i) (a i)) = monomial (∑ i ∈ t, d i) (∏ i ∈ t, a i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih => simp [hi, ih, monomial_mul_monomial]

/-- A monomial of degree `d.degree` evaluates to a Rees monomial in that degree. -/
theorem reesPresentation_monomial_coe (d : Fin s →₀ ℕ) (a : R) :
    (reesPresentation R I z hz (MvPolynomial.monomial d a) : R[X]) =
      monomial d.degree (a * d.prod fun i k => z i ^ k) := by
  change MvPolynomial.aeval (R := R) (fun i => monomial 1 (z i))
    (MvPolynomial.monomial d a) = _
  rw [MvPolynomial.aeval_monomial]
  simp only [algebraMap_apply, monomial_pow, one_mul, Finsupp.prod, prod_monomial,
    C_mul_monomial]
  rfl

/-- The image of a polynomial monomial belongs to its corresponding Rees grade. -/
theorem gradedPresentationMap_monomial_mem (d : Fin s →₀ ℕ) (c : R ⧸ I) :
    gradedPresentationMap R I z hz (MvPolynomial.monomial d c) ∈
      reesGrade R I R d.degree := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  let b := reesPresentation R I z hz (MvPolynomial.monomial d a)
  have hb : a * d.prod (fun i k => z i ^ k) ∈ I ^ d.degree := by
    have hb := b.2 d.degree
    rw [show (b : R[X]) = monomial d.degree (a * d.prod fun i k => z i ^ k)
      from reesPresentation_monomial_coe R I z hz d a, coeff_monomial_same] at hb
    exact hb
  let v : adicSubmodule R I R d.degree :=
    ⟨a * d.prod (fun i k => z i ^ k), by
      simpa only [adicSubmodule, Ideal.smul_eq_mul, Ideal.mul_top] using hb⟩
  have hv : reesModuleSelfEquiv R I (reesSingle R I R d.degree v) = b := by
    apply Subtype.ext
    rw [reesModuleSelfEquiv_reesSingle, reesPresentation_monomial_coe]
  refine ⟨Submodule.Quotient.mk v, ?_⟩
  apply (reesGradedSelfEquiv R I).injective
  rw [reesGradedSelfEquiv_gradedSingle_mk, hv]
  change Ideal.Quotient.mk _ b = reesGradedSelfEquiv R I
    ((reesGradedSelfEquiv R I).symm
      (gradedReesPresentation R I z hz (MvPolynomial.monomial d (Ideal.Quotient.mk I a))))
  rw [LinearEquiv.apply_symm_apply]
  symm
  simpa only [MvPolynomial.map_monomial] using
    gradedReesPresentation_map R I z hz (MvPolynomial.monomial d a)

/-- The presentation preserves every homogeneous degree. -/
theorem gradedPresentationMap_mem_reesGrade (n : ℕ)
    (p : MvPolynomial (Fin s) (R ⧸ I))
    (hp : p ∈ (MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ I) n).restrictScalars R) :
    gradedPresentationMap R I z hz p ∈ reesGrade R I R n := by
  classical
  change p.IsHomogeneous n at hp
  rw [MvPolynomial.as_sum p, map_sum]
  apply Submodule.sum_mem
  intro d hd
  have hdn : d.degree = n := (hp.degree_eq_sum_deg_support hd).symm
  rw [← hdn]
  exact gradedPresentationMap_monomial_mem R I z hz d (p.coeff d)

/-- The degreewise lengths over `R` agree with those over the quotient
coefficient ring, since its algebra map is surjective. -/
theorem homogeneousSubmodule_length_restrictScalars (s n : ℕ) :
    Module.length R ((MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ I) n).restrictScalars R) =
      Module.length (R ⧸ I) (MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ I) n) := by
  change Module.length R (MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ I) n) = _
  exact Module.length_eq_of_surjective (S := R) (R := R ⧸ I)
    (Ideal.Quotient.mk_surjective (I := I))

/-- The source Hilbert series is independent of restricting coefficients
from the quotient ring to `R`. -/
theorem homogeneousSubmodule_lengthSeries_restrictScalars (s : ℕ) :
    HilbertSerre.lengthSeries (fun n =>
      (MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ I) n).restrictScalars R) =
      HilbertSerre.lengthSeries (MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ I)) := by
  ext n
  simp only [HilbertSerre.lengthSeries, PowerSeries.coeff_mk,
    homogeneousSubmodule_length_restrictScalars R I s n]

/-- Every source grade over the residue field has finite length over `R`. -/
theorem isFiniteLength_homogeneousSubmodule_restrictScalars [IsLocalRing R] (s n : ℕ) :
    IsFiniteLength R
      ((MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ maximalIdeal R) n).restrictScalars R) := by
  let : IsArtinianRing (R ⧸ maximalIdeal R) :=
    inferInstanceAs (IsArtinianRing (ResidueField R))
  let : IsNoetherianRing (R ⧸ maximalIdeal R) :=
    inferInstanceAs (IsNoetherianRing (ResidueField R))
  let : IsNoetherian (R ⧸ maximalIdeal R)
      (MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ maximalIdeal R) n) :=
    isNoetherian_of_fg_of_noetherian _
      (MvPolynomial.homogeneousSubmodule_fg (Fin s) (R ⧸ maximalIdeal R) n)
  let : IsArtinian (R ⧸ maximalIdeal R)
      (MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ maximalIdeal R) n) :=
    isArtinian_of_fg_of_artinian _
      (MvPolynomial.homogeneousSubmodule_fg (Fin s) (R ⧸ maximalIdeal R) n)
  apply Module.length_ne_top_iff.mp
  rw [homogeneousSubmodule_length_restrictScalars]
  exact Module.length_ne_top

end SerrePositivity.HilbertSamuel
