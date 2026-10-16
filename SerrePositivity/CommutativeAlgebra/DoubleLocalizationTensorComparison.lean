module

public import SerrePositivity.CommutativeAlgebra.PrincipalLocalizationNormalization
public import SerrePositivity.CommutativeAlgebra.GenericEtale
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # The original algebra under two principal localizations

The comparison keeps the original map from A, rather than replacing it by an
unspecified algebra isomorphism of the localized objects.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open scoped TensorProduct
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- Base change to R[1/g] equals the standard localization of the original A. -/
def originalAwayTensorEquiv (g : R) :
    letI := GenericEtale.awayAlgebra R A g
    (Localization.Away g) ⊗[R] A ≃ₐ[Localization.Away g]
      Localization.Away (algebraMap R A g) := by
  letI := GenericEtale.awayAlgebra R A g
  letI : IsScalarTower R (Localization.Away g) (Localization.Away (algebraMap R A g)) :=
    GenericEtale.awayAlgebra_scalarTower R A g
  letI : IsLocalization (Algebra.algebraMapSubmonoid A (.powers g))
      (Localization.Away (algebraMap R A g)) := by
    rw [Algebra.algebraMapSubmonoid_powers]
    infer_instance
  letI : Algebra.IsPushout R A (Localization.Away g)
      (Localization.Away (algebraMap R A g)) :=
    Algebra.isPushout_of_isLocalization (.powers g) (Localization.Away g) A _
  letI : Algebra.IsPushout R (Localization.Away g) A
      (Localization.Away (algebraMap R A g)) := Algebra.IsPushout.symm inferInstance
  exact Algebra.IsPushout.equiv R (Localization.Away g) A _

/-- The base change equivalence uses the original localization map on A. -/
theorem originalAwayTensorEquiv_tmul (g : R) (a : A) :
    letI := GenericEtale.awayAlgebra R A g
    originalAwayTensorEquiv R A g ((1 : Localization.Away g) ⊗ₜ[R] a) =
      algebraMap A (Localization.Away (algebraMap R A g)) a := by
  simp only [originalAwayTensorEquiv, Algebra.IsPushout.equiv_tmul, map_one, one_mul]

/-- Two localizations preserve base change from the original A, with the original scalar tower. -/
def doubleLocalizationTensorEquiv (g : R) (f : Localization.Away g) :
    letI := GenericEtale.awayAlgebra R A g
    (Localization.Away f) ⊗[R] A ≃ₐ[Localization.Away f]
      (Localization.Away f) ⊗[Localization.Away g]
        (Localization.Away (algebraMap R A g)) := by
  letI := GenericEtale.awayAlgebra R A g
  letI : IsScalarTower R (Localization.Away g) (Localization.Away f) :=
    principalLocalizationTower_scalarTower g f
  exact (Algebra.TensorProduct.cancelBaseChange R (Localization.Away g)
      (Localization.Away f) (Localization.Away f) A).symm.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl :
      (Localization.Away f) ≃ₐ[Localization.Away f] (Localization.Away f))
      (originalAwayTensorEquiv R A g))

/-- The normalization fixes the value of every original element of A. -/
theorem doubleLocalizationTensorEquiv_tmul (g : R) (f : Localization.Away g) (a : A) :
    letI := GenericEtale.awayAlgebra R A g
    doubleLocalizationTensorEquiv R A g f ((1 : Localization.Away f) ⊗ₜ[R] a) =
      (1 : Localization.Away f) ⊗ₜ[Localization.Away g]
        algebraMap A (Localization.Away (algebraMap R A g)) a := by
  simp only [doubleLocalizationTensorEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    AlgEquiv.coe_toAlgHom, originalAwayTensorEquiv_tmul]
  rfl

end SerrePositivity
