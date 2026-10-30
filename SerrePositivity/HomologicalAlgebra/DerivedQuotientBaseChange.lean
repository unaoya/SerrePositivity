module
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
public import SerrePositivity.CommutativeAlgebra.Adic.ReductionScalarExtension

/-! # Derived quotient base change with ordinary residue factors -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Derived reduction agrees with the ordinary residue module under the explicit Tor condition. -/
def derivedQuotientModuleIso (M : ModuleCat.{u} R)
    (hM : scalarExtensionTorVanishing (Ideal.Quotient.mk I) M) :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj
        (boundedAboveDerivedSingleFunctor.obj M) ≅
      boundedAboveDerivedSingleFunctor.obj ((quotientModuleFunctor I).obj M) :=
  boundedAboveDerivedBaseChangeModuleAugmentationIso (Ideal.Quotient.mk I) M hM ≪≫
    boundedAboveDerivedSingleFunctor.mapIso (quotientScalarExtensionEquiv I M).toModuleIso

lemma derivedQuotientModuleIso_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hM : scalarExtensionTorVanishing (Ideal.Quotient.mk I) M)
    (hN : scalarExtensionTorVanishing (Ideal.Quotient.mk I) N) :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).map
        (boundedAboveDerivedSingleFunctor.map f) ≫ (derivedQuotientModuleIso I N hN).hom =
      (derivedQuotientModuleIso I M hM).hom ≫
        boundedAboveDerivedSingleFunctor.map ((quotientModuleFunctor I).map f) := by
  simp only [derivedQuotientModuleIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, boundedAboveDerivedBaseChangeModuleAugmentationIso_naturality
    (Ideal.Quotient.mk I) f hM hN, Category.assoc]
  simp only [Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg boundedAboveDerivedSingleFunctor.map
    ((quotientScalarExtensionIso I).hom.naturality f)

/-- Quotient base change with two ordinary residue modules; both Tor conditions are required. -/
def derivedTensorQuotientModuleIso (M N : ModuleCat.{u} R)
    (hM : scalarExtensionTorVanishing (Ideal.Quotient.mk I) M)
    (hN : scalarExtensionTorVanishing (Ideal.Quotient.mk I) N) :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N)) ≅
      boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj ((quotientModuleFunctor I).obj M),
          boundedAboveDerivedSingleFunctor.obj ((quotientModuleFunctor I).obj N)) :=
  boundedAboveDerivedTensorBaseChangeIso (Ideal.Quotient.mk I) _ _ ≪≫
    boundedAboveDerivedTensor.mapIso (Iso.prod (derivedQuotientModuleIso I M hM)
      (derivedQuotientModuleIso I N hN))

lemma derivedTensorQuotientModuleIso_naturality {M M' N N' : ModuleCat.{u} R}
    (f : M ⟶ M') (g : N ⟶ N')
    (hM : scalarExtensionTorVanishing (Ideal.Quotient.mk I) M)
    (hM' : scalarExtensionTorVanishing (Ideal.Quotient.mk I) M')
    (hN : scalarExtensionTorVanishing (Ideal.Quotient.mk I) N)
    (hN' : scalarExtensionTorVanishing (Ideal.Quotient.mk I) N') :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).map (boundedAboveDerivedTensor.map
        (boundedAboveDerivedSingleFunctor.map f, boundedAboveDerivedSingleFunctor.map g)) ≫
        (derivedTensorQuotientModuleIso I M' N' hM' hN').hom =
      (derivedTensorQuotientModuleIso I M N hM hN).hom ≫ boundedAboveDerivedTensor.map
        (boundedAboveDerivedSingleFunctor.map ((quotientModuleFunctor I).map f),
          boundedAboveDerivedSingleFunctor.map ((quotientModuleFunctor I).map g)) := by
  simp only [derivedTensorQuotientModuleIso, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom]
  rw [← Category.assoc, boundedAboveDerivedTensorBaseChangeIso_naturality, Category.assoc]
  simp only [Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  apply congrArg boundedAboveDerivedTensor.map
  apply Prod.ext
  · exact derivedQuotientModuleIso_naturality I f hM hM'
  · exact derivedQuotientModuleIso_naturality I g hN hN'

attribute [local instance] adicQuotientAlgebra

/-- For algebras this is the actual quotient ring `S / IS` as a degree-zero derived module. -/
def derivedQuotientAlgebraIso (S : Type u) [CommRing S] [Algebra R S]
    (hS : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R S)) :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S)) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of (R ⧸ I) (S ⧸ I.map (algebraMap R S))) :=
  boundedAboveDerivedBaseChangeModuleAugmentationIso (Ideal.Quotient.mk I) (ModuleCat.of R S) hS ≪≫
    boundedAboveDerivedSingleFunctor.mapIso (quotientAlgebraScalarExtensionEquiv I S).toModuleIso

lemma derivedQuotientAlgebraIso_naturality {S T : Type u} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (f : S →ₐ[R] T)
    (hS : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R T)) :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).map
        (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap)) ≫
        (derivedQuotientAlgebraIso I T hT).hom =
      (derivedQuotientAlgebraIso I S hS).hom ≫
        boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (adicAlgebraReductionMap I f)) := by
  simp only [derivedQuotientAlgebraIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, boundedAboveDerivedBaseChangeModuleAugmentationIso_naturality
    (Ideal.Quotient.mk I) (ModuleCat.ofHom f.toLinearMap) hS hT, Category.assoc]
  simp only [Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg boundedAboveDerivedSingleFunctor.map
    (quotientAlgebraScalarExtensionEquiv_naturality I f)

/-- The ring-quotient form of tensor base change, retaining the two independent Tor hypotheses. -/
def derivedTensorQuotientAlgebraIso (S T : Type u) [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (hS : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R T)) :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S),
        boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T))) ≅
      boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of (R ⧸ I) (S ⧸ I.map (algebraMap R S))),
          boundedAboveDerivedSingleFunctor.obj
            (ModuleCat.of (R ⧸ I) (T ⧸ I.map (algebraMap R T)))) :=
  boundedAboveDerivedTensorBaseChangeIso (Ideal.Quotient.mk I) _ _ ≪≫
    boundedAboveDerivedTensor.mapIso (Iso.prod (derivedQuotientAlgebraIso I S hS)
      (derivedQuotientAlgebraIso I T hT))

lemma derivedTensorQuotientAlgebraIso_naturality
    {S S' T T' : Type u} [CommRing S] [CommRing S'] [CommRing T] [CommRing T']
    [Algebra R S] [Algebra R S'] [Algebra R T] [Algebra R T']
    (f : S →ₐ[R] S') (g : T →ₐ[R] T')
    (hS : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R S))
    (hS' : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R S'))
    (hT : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R T))
    (hT' : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R T')) :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).map (boundedAboveDerivedTensor.map
        (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap),
          boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom g.toLinearMap))) ≫
        (derivedTensorQuotientAlgebraIso I S' T' hS' hT').hom =
      (derivedTensorQuotientAlgebraIso I S T hS hT).hom ≫ boundedAboveDerivedTensor.map
        (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (adicAlgebraReductionMap I f)),
          boundedAboveDerivedSingleFunctor.map
            (ModuleCat.ofHom (adicAlgebraReductionMap I g))) := by
  simp only [derivedTensorQuotientAlgebraIso, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom]
  rw [← Category.assoc, boundedAboveDerivedTensorBaseChangeIso_naturality, Category.assoc]
  simp only [Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  apply congrArg boundedAboveDerivedTensor.map
  apply Prod.ext
  · exact derivedQuotientAlgebraIso_naturality I f hS hS'
  · exact derivedQuotientAlgebraIso_naturality I g hT hT'

end SerrePositivity
