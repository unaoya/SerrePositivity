module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.AlgebraBaseChangeTensorUnit
public import SerrePositivity.BhattScholze.CompletedTensorPerfectoidization

/-! # Prop 2.4.7：元の完備底変換単位と BS の通常 tensor 写像

この単位の一致自体には perfectoid 性・平坦性・有限性を要求しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R B S : Type u) [CommRing R] [CommRing B] [CommRing S]
    [Algebra R B] [Algebra R S] (p : ℕ)

/-- 元の完備底変換単位は、元の B 線形 H⁰ 比較を通して BS の通常 tensor 写像となる。 -/
theorem prop247_completedBaseChangeTensorH0_unit
    (x : (DerivedCategory.homologyFunctor (ModuleCat B) 0).obj
      ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) B S)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) B S)
    letI := completedTensorH0LeftAlgebra R (p : R) B S
    completedBaseChangeTensorH0LinearEquiv R B S (p : R)
        ((DerivedCategory.homologyFunctor (ModuleCat B) 0).map
          ((derivedComplexCompletionUnit B (algebraMap R B (p : R))).app
            ((boundedAboveDerivedBaseChange (algebraMap R B)).obj
              (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S))).obj) x) =
      BhattScholze.completedTensorPerfectoidizationMap R p B S
        ((algebraScalarExtensionModuleIso R B (ModuleCat.of R S)).hom
          ((boundedAboveDerivedBaseChangeModuleH0Iso (algebraMap R B)).hom.app
            (ModuleCat.of R S) x)) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) B S)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) B S)
  let := completedTensorH0LeftAlgebra R (p : R) B S
  let := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R) B S)
  let := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := R) B S)
  rw [completedBaseChangeTensorH0LinearEquiv_apply, completedBaseChangeTensorH0Iso_unit_apply,
    BhattScholze.completedTensorPerfectoidizationMap_apply, derivedH0AlgMap_apply,
    boundedAboveCompletionAlgebraUnit_hom]
  change (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((derivedComplexCompletionUnit R (p : R)).app
        (boundedAboveDerivedTensorAlgebra (R := R) B S).X.obj)
      ((algebraBaseChangeTensorH0Iso R B S).hom x) =
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((derivedComplexCompletionUnit R (p : R)).app
        (boundedAboveDerivedTensorAlgebra (R := R) B S).X.obj) _
  apply congrArg
  apply (derivedTensorH0AlgEquiv (R := R) B S).injective
  rw [AlgEquiv.apply_symm_apply]
  exact algebraBaseChangeTensorH0Iso_apply R B S x

end SerrePositivity.CLMST
