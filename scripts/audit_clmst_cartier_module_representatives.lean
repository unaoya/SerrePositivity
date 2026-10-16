import SerrePositivity.HomologicalAlgebra.PureDerivedCartierModuleRepresentatives
import SerrePositivity.HomologicalAlgebra.DerivedTensorPureFactorization
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionAlgebraObjects
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso_hom_normalized
assert_no_sorry SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso_module_representative
assert_no_sorry SerrePositivity.derivedTensorAlgebraMap_factor_pure

#print axioms SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso_hom_normalized
#print axioms SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso_module_representative
#print axioms SerrePositivity.derivedTensorAlgebraMap_factor_pure

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
open scoped TensorProduct ChangeOfRings
attribute [local instance] HasDerivedCategory.standard principalAdicQuotientAlgebra

-- The source is killed by d; no source d-regularity or quotient Tor condition is supplied.
example (R : Type u) [CommRing R] (d : R) (hd : IsSMulRegular R d)
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R)))
    [A.X.obj.IsGE 0] [A.X.obj.IsLE 0]
    (hA : IsSMulRegular ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) d)
    (m : R ⧸ Ideal.span {d}) :
    let H := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj
    let M := ModuleCat.of R (R ⧸ Ideal.span {d})
    let Q := R ⧸ Ideal.span {d}
    let q := Ideal.Quotient.mk (Ideal.span {d})
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    (pureDerivedAlgebraCartierQuotientH0Iso R d hd A hA).hom
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          (((boundedAboveDerivedBaseChange q).map
            (boundedAboveDerivedSingleFunctor.map (0 : M ⟶ H) ≫
              (pureDerivedAlgebraSingleIso R A).inv)).hom)
          ((boundedAboveDerivedBaseChangeModuleH0Iso q).inv.app M ((1 : Q) ⊗ₜ[R,q] m))) = 0 := by
  let H := (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj
  let M := ModuleCat.of R (R ⧸ Ideal.span {d})
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  have h := pureDerivedAlgebraCartierQuotientH0Iso_module_representative R d hd A hA M
    (0 : M ⟶ H) m
  simpa only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero] using h

-- The original two completion units factor through the original tensor augmentation.
example (R : Type u) [CommRing R] (a d : R) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    let B := boundedAboveDerivedTensorAlgebra (R := R) S T
    let AP := boundedAboveCompletedTensorAlgebra R a S T
    let AD := (boundedAboveCompletionCommMonFunctor R d).obj AP
    ∀ (hpure : AD.X.obj.IsGE 0 ∧ AD.X.obj.IsLE 0),
    letI : AD.X.obj.IsGE 0 := hpure.1
    letI : AD.X.obj.IsLE 0 := hpure.2
    letI := derivedH0CommRing B
    letI := derivedH0Algebra B
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    let f := boundedAboveCompletionAlgebraUnit R a B ≫ boundedAboveCompletionAlgebraUnit R d AP
    let e : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj B.X.obj ≃ₐ[R] S ⊗[R] T :=
      derivedTensorH0AlgEquiv (R := R) S T
    let g := (derivedH0AlgMap f).comp e.symm.toAlgHom
    f.hom.hom = (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom ≫
      boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom g.toLinearMap) ≫
      (pureDerivedAlgebraSingleIso R AD).inv := by
  dsimp only
  intro hpure
  let B := boundedAboveDerivedTensorAlgebra (R := R) S T
  let AP := boundedAboveCompletedTensorAlgebra R a S T
  let AD := (boundedAboveCompletionCommMonFunctor R d).obj AP
  let : AD.X.obj.IsGE 0 := hpure.1
  let : AD.X.obj.IsLE 0 := hpure.2
  let := derivedH0CommRing B
  let := derivedH0Algebra B
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  exact derivedTensorAlgebraMap_factor_pure R S T AD
    (boundedAboveCompletionAlgebraUnit R a B ≫ boundedAboveCompletionAlgebraUnit R d AP)
