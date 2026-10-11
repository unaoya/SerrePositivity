module

public import SerrePositivity.CommutativeAlgebra.ReesPresentation

/-!
# Identifying the self Rees module with the Rees algebra

The polynomial module of the ring itself is its polynomial ring. Restricting this
identification to Rees objects identifies their shifted denominators, hence also
their associated graded quotients. No Noetherian or regularity hypothesis is needed.
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.HilbertSamuel

open Polynomial PolynomialModule

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Ideal R)

@[simp]
theorem coeff_equivPolynomialSelf (f : PolynomialModule R R) (n : ℕ) :
    (equivPolynomialSelf f).coeff n = f.coeff n := rfl

@[simp]
theorem coeff_equivPolynomialSelf_symm (f : R[X]) (n : ℕ) :
    (equivPolynomialSelf.symm f).coeff n = f.coeff n := rfl

/-- The Rees module of the ring is the Rees algebra, linearly over that algebra. -/
def reesModuleSelfEquiv : ReesModule R I R ≃ₗ[reesAlgebra I] reesAlgebra I where
  toFun f := ⟨equivPolynomialSelf f.1, by
    intro n
    change f.1.coeff n ∈ I ^ n
    have hf := f.2 n
    change f.1.coeff n ∈ I ^ n • (⊤ : Submodule R R) at hf
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hf⟩
  invFun f := ⟨equivPolynomialSelf.symm f.1, by
    intro n
    change f.1.coeff n ∈ I ^ n • (⊤ : Submodule R R)
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using f.2 n⟩
  left_inv f := by
    apply Subtype.ext
    exact equivPolynomialSelf.symm_apply_apply f.1
  right_inv f := by
    apply Subtype.ext
    exact equivPolynomialSelf.apply_symm_apply f.1
  map_add' f g := by
    apply Subtype.ext
    exact map_add equivPolynomialSelf f.1 g.1
  map_smul' a f := by
    apply Subtype.ext
    change equivPolynomialSelf (a.1 • f.1) = a.1 * equivPolynomialSelf f.1
    exact equivPolynomialSelf.map_smul a.1 f.1

@[simp]
theorem reesModuleSelfEquiv_coeff (f : ReesModule R I R) (n : ℕ) :
    (reesModuleSelfEquiv R I f : R[X]).coeff n = f.1.coeff n := rfl

/-- The shifted Rees denominator corresponds to the image of the coefficient ideal. -/
theorem mem_reesDenominator_iff_self (f : ReesModule R I R) :
    f ∈ reesDenominator R I R ↔
      reesModuleSelfEquiv R I f ∈ I.map (algebraMap R (reesAlgebra I)) := by
  rw [mem_reesDenominator, mem_map_algebraMap_reesAlgebra_iff]
  simp only [reesModuleSelfEquiv_coeff, adicSubmodule, Ideal.smul_eq_mul, Ideal.mul_top]

/-- The denominator is sent onto the coefficient ideal in the Rees algebra. -/
theorem reesDenominator_map_self :
    (reesDenominator R I R).map (reesModuleSelfEquiv R I).toLinearMap =
      I.map (algebraMap R (reesAlgebra I)) := by
  ext f
  rw [Submodule.mem_map]
  refine ⟨fun ⟨g, hg, hgf⟩ => hgf ▸ (mem_reesDenominator_iff_self R I g).mp hg, ?_⟩
  intro hf
  refine ⟨(reesModuleSelfEquiv R I).symm f, ?_, (reesModuleSelfEquiv R I).apply_symm_apply f⟩
  exact (mem_reesDenominator_iff_self R I _).mpr (by simpa using hf)

/-- The self associated graded module is the associated graded ring, linearly over the
Rees algebra. -/
def reesGradedSelfEquiv : ReesGraded R I R ≃ₗ[reesAlgebra I] GradedReesRing R I :=
  Submodule.Quotient.equiv _ _ (reesModuleSelfEquiv R I) (reesDenominator_map_self R I)

@[simp]
theorem reesGradedSelfEquiv_mk (f : ReesModule R I R) :
    reesGradedSelfEquiv R I (Submodule.Quotient.mk f) =
      Ideal.Quotient.mk _ (reesModuleSelfEquiv R I f) := rfl

/-- The same identification is linear over the associated graded ring itself. -/
def reesGradedSelfEquivOverGradedRing :
    ReesGraded R I R ≃ₗ[GradedReesRing R I] GradedReesRing R I where
  toAddEquiv := (reesGradedSelfEquiv R I).toAddEquiv
  map_smul' a x := by
    obtain ⟨r, rfl⟩ := (Ideal.Quotient.mk_surjective
      (I := I.map (algebraMap R (reesAlgebra I)))) a
    change reesGradedSelfEquiv R I
      (@SMul.smul (reesAlgebra I) (ReesGraded R I R) _ r x) =
      @SMul.smul (reesAlgebra I) (GradedReesRing R I) _ r (reesGradedSelfEquiv R I x)
    exact (reesGradedSelfEquiv R I).map_smul r x

@[simp]
theorem reesGradedSelfEquivOverGradedRing_apply (x : ReesGraded R I R) :
    reesGradedSelfEquivOverGradedRing R I x = reesGradedSelfEquiv R I x := rfl

/-- The self Rees monomial corresponds to the ring monomial of the same degree. -/
@[simp]
theorem reesModuleSelfEquiv_reesSingle (n : ℕ) (x : adicSubmodule R I R n) :
    (reesModuleSelfEquiv R I (reesSingle R I R n x) : R[X]) = monomial n (x : R) := by
  change equivPolynomialSelf (single R n (x : R)) = monomial n (x : R)
  rw [equivPolynomialSelf_apply_eq, equivPolynomial_single]

/-- A homogeneous element is sent to its monomial class in the associated graded ring. -/
@[simp]
theorem reesGradedSelfEquiv_gradedSingle_mk (n : ℕ) (x : adicSubmodule R I R n) :
    reesGradedSelfEquiv R I (gradedSingle R I R n (Submodule.Quotient.mk x)) =
      Ideal.Quotient.mk _ (reesModuleSelfEquiv R I (reesSingle R I R n x)) := rfl

end SerrePositivity.HilbertSamuel
