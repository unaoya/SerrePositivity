module
public import SerrePositivity.HomologicalAlgebra.DerivedTensorSymmetry
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeTensor
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientBaseChange

/-! # Derived base change in the right scalar-factor convention -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]
local notation "D" => DerivedCategory.Minus (ModuleCat R)

/-- Restricted scalar extension is right tensor with the scalar ring, naturally in the input. -/
def boundedAboveDerivedBaseChangeRightTensorNatIso (φ : R →+* S) :
    boundedAboveDerivedBaseChange φ ⋙ boundedAboveDerivedRestrictScalars φ ≅
      ((𝟭 D).prod' ((Functor.const D).obj (derivedBaseChangeScalarObject φ))) ⋙
        boundedAboveDerivedTensor :=
  boundedAboveDerivedBaseChangeTensorNatIso φ ≪≫
    (boundedAboveDerivedTensorSwapNatIso (derivedBaseChangeScalarObject φ)).symm

/-- The tensor base-change formula with the coefficient ring on the right.
Both factors on the new base remain derived; no flatness assumptions are imposed. -/
def restrictedDerivedTensorBaseChangeRightNatIso (φ : R →+* S) :
    boundedAboveDerivedTensor ⋙
        (((𝟭 D).prod' ((Functor.const D).obj (derivedBaseChangeScalarObject φ))) ⋙
          boundedAboveDerivedTensor) ≅
      ((boundedAboveDerivedBaseChange φ).prod (boundedAboveDerivedBaseChange φ)) ⋙
        boundedAboveDerivedTensor ⋙ boundedAboveDerivedRestrictScalars φ :=
  Functor.isoWhiskerLeft _
      (boundedAboveDerivedTensorSwapNatIso (derivedBaseChangeScalarObject φ)) ≪≫
    restrictedDerivedTensorBaseChangeNatIso φ

attribute [local instance] adicQuotientAlgebra

/-- Specialize right scalar tensor to a quotient, retaining both Tor-vanishing hypotheses. -/
def restrictedDerivedTensorQuotientAlgebraIso (I : Ideal R)
    (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (hA : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R A))
    (hB : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R B)) :
    boundedAboveDerivedTensor.obj
        (boundedAboveDerivedTensor.obj (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A),
          boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R B)),
          derivedBaseChangeScalarObject (Ideal.Quotient.mk I)) ≅
      (boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk I)).obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj
            (ModuleCat.of (R ⧸ I) (A ⧸ I.map (algebraMap R A))),
           boundedAboveDerivedSingleFunctor.obj
            (ModuleCat.of (R ⧸ I) (B ⧸ I.map (algebraMap R B))))) :=
  ((boundedAboveDerivedBaseChangeRightTensorNatIso (Ideal.Quotient.mk I)).app _).symm ≪≫
    (boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk I)).mapIso
      (derivedTensorQuotientAlgebraIso I A B hA hB)

/-- The right scalar-factor quotient comparison is natural in both algebra maps. -/
lemma restrictedDerivedTensorQuotientAlgebraIso_naturality (I : Ideal R)
    {A A' B B' : Type u} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra R A] [Algebra R A'] [Algebra R B] [Algebra R B']
    (f : A →ₐ[R] A') (g : B →ₐ[R] B')
    (hA : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R A))
    (hA' : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R A'))
    (hB : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R B))
    (hB' : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R B')) :
    boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
        (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap))
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom g.toLinearMap))))
        (𝟙 (derivedBaseChangeScalarObject (Ideal.Quotient.mk I)))) ≫
      (restrictedDerivedTensorQuotientAlgebraIso I A' B' hA' hB').hom =
    (restrictedDerivedTensorQuotientAlgebraIso I A B hA hB).hom ≫
      (boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk I)).map
        (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (adicAlgebraReductionMap I f)))
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom
            (adicAlgebraReductionMap I g))))) := by
  let q := Ideal.Quotient.mk I
  let t := boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
    (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom f.toLinearMap))
    (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom g.toLinearMap)))
  have hn := (boundedAboveDerivedBaseChangeRightTensorNatIso q).inv.naturality t
  change boundedAboveDerivedTensor.map
      (CategoryTheory.Prod.mkHom t (𝟙 (derivedBaseChangeScalarObject q))) ≫
        ((boundedAboveDerivedBaseChangeRightTensorNatIso q).app _).inv =
      ((boundedAboveDerivedBaseChangeRightTensorNatIso q).app _).inv ≫
        (boundedAboveDerivedRestrictScalars q).map
          ((boundedAboveDerivedBaseChange q).map t) at hn
  have hq := derivedTensorQuotientAlgebraIso_naturality I f g hA hA' hB hB'
  simp only [restrictedDerivedTensorQuotientAlgebraIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  change _ ≫ ((boundedAboveDerivedBaseChangeRightTensorNatIso q).app _).inv ≫ _ = _
  rw [← Category.assoc, hn, Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (boundedAboveDerivedRestrictScalars q).map hq

end SerrePositivity
