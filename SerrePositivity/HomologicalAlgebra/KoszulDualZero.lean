module
public import SerrePositivity.HomologicalAlgebra.ChainLinearYonedaZero
public import SerrePositivity.HomologicalAlgebra.KoszulExtComparison

/-! # Zero dual Koszul cohomology as Hom from the actual parameter quotient -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex DerivedCompletion
variable {R : Type u} [CommRing R] {e : ℕ} (z : Fin e → R)

/-- The chain zero-homology normalization uses the actual standard Koszul quotient map. -/
def koszulChainCanonicalH0Iso :
    (toChain (koszulComplex z)).homology 0 ≅ ModuleCat.of R (R ⧸ Ideal.span (Set.range z)) :=
  toChainHomologyIso (koszulComplex z) (koszulComplex_isZero_X_of_pos z) 0 ≪≫
    (koszulCanonicalH0Equiv R z).toModuleIso

/-- Zero dual Koszul cohomology is the actual quotient-Hom functor, naturally in coefficients.
Neither a regularity hypothesis on z nor an injectivity hypothesis on coefficients is used. -/
def koszulDualZeroHomologyNatIso :
    koszulDualModuleFunctor z ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℕ) 0 ≅
      (linearCoyoneda R (ModuleCat.{u} R)).obj
        (op (ModuleCat.of R (R ⧸ Ideal.span (Set.range z)))) :=
  chainLinearYonedaZeroHomologyNatIso (toChain (koszulComplex z)) ≪≫
    ((linearCoyoneda R (ModuleCat.{u} R)).mapIso (koszulChainCanonicalH0Iso z).op).symm

end SerrePositivity
