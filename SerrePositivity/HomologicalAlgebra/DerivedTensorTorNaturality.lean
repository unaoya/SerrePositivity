module

public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleComparison

/-! # Actual derived-tensor homology and Tor agree on coefficient maps -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- The actual negative-degree homology comparison preserves every original
coefficient map, including multiplication by an algebra element. -/
@[reassoc] lemma boundedAboveDerivedTensorModuleTorIso_naturality_left
    {C D : ModuleCat.{u} R} (f : C ⟶ D) (N : ModuleCat.{u} R) (i : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat R) (-(i : ℤ))).map
      (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
        (boundedAboveDerivedSingleFunctor.map f)
        (𝟙 (boundedAboveDerivedSingleFunctor.obj N)))).hom ≫
        (boundedAboveDerivedTensorModuleTorNatIso D i).hom.app N =
      (boundedAboveDerivedTensorModuleTorNatIso C i).hom.app N ≫
        ((Tor (ModuleCat R) i).map f).app N := by
  let H := DerivedCategory.homologyFunctor (ModuleCat R) (-(i : ℤ))
  let α := (NatTrans.leftDerivedToHomotopyCategory
    ((tensoringLeft (ModuleCat R)).map f)).app N
  have hb := congrArg H.map (boundedAboveDerivedTensorModuleIso_naturality_left f N)
  simp only [Functor.map_comp] at hb
  have ht := (chainDerivedRealizationHomologyIso R i).hom.naturality α
  change H.map ((chainDerivedRealization R).map α) ≫
    ((chainDerivedRealizationHomologyIso R i).hom.app
      (((tensorLeft D).leftDerivedToHomotopyCategory).obj N)) =
    (chainDerivedRealizationHomologyIso R i).hom.app
      (((tensorLeft C).leftDerivedToHomotopyCategory).obj N) ≫
        ((Tor (ModuleCat R) i).map f).app N at ht
  have ht' : H.map ((realizedDerivedTensorMapLeft R f).app N) ≫
      (chainDerivedRealizationHomologyIso R i).hom.app
        (((tensorLeft D).leftDerivedToHomotopyCategory).obj N) =
    (chainDerivedRealizationHomologyIso R i).hom.app
      (((tensorLeft C).leftDerivedToHomotopyCategory).obj N) ≫
        ((Tor (ModuleCat R) i).map f).app N := ht
  change H.map _ ≫ (H.map (boundedAboveDerivedTensorModuleIso D N).hom ≫
      (chainDerivedRealizationHomologyIso R i).hom.app
        (((tensorLeft D).leftDerivedToHomotopyCategory).obj N)) =
    (H.map (boundedAboveDerivedTensorModuleIso C N).hom ≫
      (chainDerivedRealizationHomologyIso R i).hom.app
        (((tensorLeft C).leftDerivedToHomotopyCategory).obj N)) ≫ _
  rw [← Category.assoc, hb, Category.assoc]
  rw [ht', Category.assoc]

end SerrePositivity
