module

public import SerrePositivity.CommutativeAlgebra.GenericEtale

/-! # Etaleness away from an original base element after arbitrary base change

The target uses the specified standard localization algebra over the new base.
No flatness of the base change is required.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- Base change preserves etaleness away from the image of the same original
base element, for the standard source and target localization algebra structures. -/
theorem etaleAway_tensor_baseChange
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (g : R) :
    letI := GenericEtale.awayAlgebra R A g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R A g)) →
      letI := GenericEtale.awayAlgebra B (B ⊗[R] A) (algebraMap R B g)
      Algebra.Etale (Localization.Away (algebraMap R B g))
        (Localization.Away (algebraMap B (B ⊗[R] A) (algebraMap R B g))) := by
  let := GenericEtale.awayAlgebra R A g
  intro hetale
  let : Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R A g)) := hetale
  let : IsScalarTower R (Localization.Away g) (Localization.Away (algebraMap R A g)) :=
    GenericEtale.awayAlgebra_scalarTower R A g
  let : Algebra.Etale R (Localization.Away g) := Algebra.Etale.of_isLocalizationAway g
  let : Algebra.Etale R (Localization.Away (algebraMap R A g)) :=
    Algebra.Etale.comp R (Localization.Away g) (Localization.Away (algebraMap R A g))
  let e := IsLocalization.Away.tensorProductEquivTMulRight R B (algebraMap R A g)
    (Localization.Away (algebraMap R A g))
  have hd : ((1 : B) ⊗ₜ[R] algebraMap R A g) =
      algebraMap B (B ⊗[R] A) (algebraMap R B g) := by
    change (1 : B) ⊗ₜ[R] algebraMap R A g = algebraMap R B g ⊗ₜ[R] (1 : A)
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul g).symm
  have htarget : Algebra.Etale B
      (Localization.Away (algebraMap B (B ⊗[R] A) (algebraMap R B g))) := by
    rw [← hd]
    exact Algebra.Etale.of_equiv e
  let := GenericEtale.awayAlgebra B (B ⊗[R] A) (algebraMap R B g)
  let : IsScalarTower B (Localization.Away (algebraMap R B g))
      (Localization.Away (algebraMap B (B ⊗[R] A) (algebraMap R B g))) :=
    GenericEtale.awayAlgebra_scalarTower B (B ⊗[R] A) (algebraMap R B g)
  let : Algebra.Etale B (Localization.Away (algebraMap R B g)) :=
    Algebra.Etale.of_isLocalizationAway (algebraMap R B g)
  let := htarget
  exact Algebra.Etale.of_restrictScalars B (Localization.Away (algebraMap R B g))
    (Localization.Away (algebraMap B (B ⊗[R] A) (algebraMap R B g)))

end SerrePositivity
