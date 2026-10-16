import SerrePositivity.HomologicalAlgebra.PureDerivedCartierSingle
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.normalizedPureHomologyIso_single
assert_no_sorry SerrePositivity.singleH0_isSMulRegular
assert_no_sorry SerrePositivity.pureDerivedAlgebraSingleIso_single
assert_no_sorry SerrePositivity.pureDerivedAlgebraCartierQuotientIso_single
assert_no_sorry SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso_single

#print axioms SerrePositivity.normalizedPureHomologyIso_single
#print axioms SerrePositivity.singleH0_isSMulRegular
#print axioms SerrePositivity.pureDerivedAlgebraSingleIso_single
#print axioms SerrePositivity.pureDerivedAlgebraCartierQuotientIso_single
#print axioms SerrePositivity.pureDerivedAlgebraCartierQuotientH0Iso_single

noncomputable section
universe u
open CategoryTheory SerrePositivity
attribute [local instance] HasDerivedCategory.standard principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]

-- Normalization works in nonzero degree, not only in the degree-zero special case.
example (M : ModuleCat.{u} R) :
    normalizedPureHomologyIso ((DerivedCategory.singleFunctor (ModuleCat R) (-2)).obj M) (-2) =
      (DerivedCategory.singleFunctor (ModuleCat R) (-2)).mapIso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (-2)).app M).symm :=
  normalizedPureHomologyIso_single (-2) M

-- Regularity of the base scalar on the ring R is not required for this transfer.
example (d : R) (hS : IsSMulRegular S d) :
    IsSMulRegular ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S))) d :=
  singleH0_isSMulRegular R d (ModuleCat.of R S) hS

-- The complete single-ring H⁰ diagram includes a unit scalar and hence a zero quotient base.
example (d : R) (hd : d = 1) :
    let hR : IsSMulRegular R d := by subst d; intro x y h; simpa only [one_smul] using h
    let hS : IsSMulRegular S d := by subst d; intro x y h; simpa only [one_smul] using h

    letI hge : (boundedAboveDerivedAlgebra (R := R) S).X.obj.IsGE 0 := by
      change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsGE 0
      infer_instance
    letI hle : (boundedAboveDerivedAlgebra (R := R) S).X.obj.IsLE 0 := by
      change ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R S)).IsLE 0
      infer_instance
    letI := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) S)
    letI := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) S)
    let eS : ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj) ≃ₐ[R] S := derivedSingleH0AlgEquiv (R := R) S
    (pureDerivedAlgebraCartierQuotientH0Iso R d hR (boundedAboveDerivedAlgebra (R := R) S)
        (singleH0_isSMulRegular R d (ModuleCat.of R S) hS)).hom ≫
        ModuleCat.ofHom (principalAdicReductionAlgHom R d eS.toAlgHom).toLinearMap =
      (DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {d})) 0).map
          (derivedQuotientModuleIsoOfRegular d hR (ModuleCat.of R S) hS).hom.hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat (R ⧸ Ideal.span {d})) 0).hom.app
          ((quotientModuleFunctor (Ideal.span {d})).obj (ModuleCat.of R S)) ≫
        (principalAdicReductionEquiv d S).toModuleIso.hom := by
  dsimp only
  exact pureDerivedAlgebraCartierQuotientH0Iso_single R S d
    (by subst d; intro x y h; simpa only [one_smul] using h)
    (by subst d; intro x y h; simpa only [one_smul] using h)
