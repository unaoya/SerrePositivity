module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletelyFlat.Definition
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletelyFlat.Definition


public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.PowerTorsion

import SerrePositivity.HomologicalAlgebra.DerivedQuotientBaseChange

/-!
離散な完全平坦加群の導来対象

可換環の実際の導来完備化と導来対象を用いる。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open CategoryTheory CategoryTheory.Limits DerivedCompletion
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra

variable {A : Type u} [CommRing A]

private theorem discrete_completelyFlat (I : Ideal A) (M : ModuleCat.{u} A)
    (hf : IsCompletelyFlat I M) :
    IsDerivedCompletelyFlat I (boundedAboveDerivedSingleFunctor.obj M) := by
  let q := Ideal.Quotient.mk I
  let N := baseChangeScalarModule q
  have hN (a : A) (ha : a ∈ I) (x : N) : a • x = 0 := by
    change q a * (show A ⧸ I from x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul]
  have htor : scalarExtensionTorVanishing q M := by
    intro n hn
    have hz := (isConcentratedInDegreeZero_derivedTensor_iff M N).mp (hf N hN) n hn
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact (torModuleComm (R := A) n N M).injective.subsingleton
  let e := DerivedCategory.Minus.ι.mapIso (derivedQuotientModuleIso I M htor)
  unfold IsDerivedCompletelyFlat
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · exact (derivedSingleHomology_isZero ((quotientModuleFunctor I).obj M) i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ I)) i).mapIso e)
  · let eh := (DerivedCategory.homologyFunctor (ModuleCat (A ⧸ I)) 0).mapIso e ≪≫
        (realizedSingleH0Iso (A ⧸ I)).app ((quotientModuleFunctor I).obj M)
    let := flat_residueTensor_of_completelyFlat I M hf
    have : Module.Flat (A ⧸ I) ((quotientModuleFunctor I).obj M) :=
      Module.Flat.of_linearEquiv (quotientTensorReductionEquiv I M).symm
    let l : ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ I)) 0).obj
        ((boundedAboveDerivedBaseChange q).obj (boundedAboveDerivedSingleFunctor.obj M)).obj)
          ≃ₗ[A ⧸ I] ((quotientModuleFunctor I).obj M) := eh.toLinearEquiv
    exact Module.Flat.of_linearEquiv l

end SerrePositivity.BhattScholze.Prismatic
