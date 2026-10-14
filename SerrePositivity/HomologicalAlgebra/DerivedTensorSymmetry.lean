module
public import SerrePositivity.HomologicalAlgebra.DerivedTensorMonoidal
public import SerrePositivity.HomologicalAlgebra.TensorBaseChangeNaturality

/-! # Natural signed factor exchange for the bounded-above derived tensor -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]
local notation "D" => DerivedCategory.Minus (ModuleCat R)
local notation "T" => boundedAboveDerivedTensor (R := R)

/-- Naturality of signed factor exchange, available in the common homological layer. -/
lemma cochainTensorSymmetry_natural {P P' Q Q' : CochainComplex (ModuleCat R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    cochainTensorMap f g ≫ (cochainTensorSymmetry P' Q').hom =
      (cochainTensorSymmetry P Q).hom ≫ cochainTensorMap g f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    cochainTensorMap_homogeneous_assoc, ιTensorObj_cochainTensorSymmetry,
    ← Category.assoc, ιTensorObj_cochainTensorSymmetry]
  rw [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
    cochainTensorMap_homogeneous]
  simp only [BraidedCategory.braiding_naturality_assoc]

/-- Exchange the factors of actual derived objects by the signed complex symmetry. -/
def boundedAboveDerivedTensorSymmetry (X Y : D) : (T).obj (X, Y) ≅ (T).obj (Y, X) :=
  ObjectProperty.isoMk _ (DerivedCategory.Q.mapIso (cochainTensorSymmetry
    (boundedAboveDerivedChosenModel X).complex (boundedAboveDerivedChosenModel Y).complex))

/-- Factor exchange commutes with arbitrary derived morphisms in both arguments. -/
lemma boundedAboveDerivedTensorSymmetry_naturality {X X' Y Y' : D}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (T).map (CategoryTheory.Prod.mkHom f g) ≫ (boundedAboveDerivedTensorSymmetry X' Y').hom =
      (boundedAboveDerivedTensorSymmetry X Y).hom ≫ (T).map (CategoryTheory.Prod.mkHom g f) := by
  apply InducedCategory.hom_ext
  change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ =
    DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg DerivedCategory.Q.map (cochainTensorSymmetry_natural _ _)

/-- Exchanging derived factors twice gives the identity. -/
lemma boundedAboveDerivedTensorSymmetry_hom_comp (X Y : D) :
    (boundedAboveDerivedTensorSymmetry X Y).hom ≫
      (boundedAboveDerivedTensorSymmetry Y X).hom = 𝟙 _ := by
  apply InducedCategory.hom_ext
  change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ = 𝟙 _
  rw [← CategoryTheory.Functor.map_comp, cochainTensorSymmetry_hom_comp,
    CategoryTheory.Functor.map_id]

/-- Move a fixed scalar object from the right tensor factor to the left, naturally. -/
def boundedAboveDerivedTensorSwapNatIso (A : D) :
    ((𝟭 D).prod' ((Functor.const D).obj A)) ⋙ (T) ≅
      (((Functor.const D).obj A).prod' (𝟭 D)) ⋙ (T) :=
  NatIso.ofComponents (fun X => boundedAboveDerivedTensorSymmetry X A)
    (fun f => boundedAboveDerivedTensorSymmetry_naturality f (𝟙 A))

end SerrePositivity
