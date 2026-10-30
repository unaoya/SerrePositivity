module
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedAssociator

/-! # Unit of the bounded-above derived tensor product -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]
local notation "D" => DerivedCategory.Minus (ModuleCat R)
local notation "T" => boundedAboveDerivedTensor (R := R)

/-- The tensor unit is the actual derived image of the degree-zero unit complex. -/
def boundedAboveDerivedTensorUnit : D :=
  ⟨DerivedCategory.Q.obj (cochainTensorUnit (R := R)), ⟨0, inferInstance⟩⟩

/-- This unit is the usual `R[0]`, with the standard module structure. -/
def boundedAboveDerivedTensorUnitSingleIso :
    (boundedAboveDerivedTensorUnit (R := R)).obj ≅
      (DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R) := Iso.refl _

/-- The unit needs no resolution: its single nonzero term is free of rank one. -/
def boundedAboveDerivedTensorUnitModel :
    BoundedAboveDerivedModel (boundedAboveDerivedTensorUnit (R := R)).obj where
  complex := cochainTensorUnit
  bound := 0
  bounded := inferInstance
  projective _ := inferInstance
  iso := Iso.refl _

/-- Left unit comparison in the standard derived category. -/
def boundedAboveDerivedTensorLeftUnitor (X : D) :
    (T).obj (boundedAboveDerivedTensorUnit, X) ≅ X :=
  ObjectProperty.isoMk _
    (boundedAboveDerivedTensorModelIso _ _ boundedAboveDerivedTensorUnitModel
      (boundedAboveDerivedChosenModel X) ≪≫
      DerivedCategory.Q.mapIso
        (cochainTensorLeftUnitor (boundedAboveDerivedChosenModel X).complex) ≪≫
      (boundedAboveDerivedChosenModel X).iso)

/-- Right unit comparison in the standard derived category. -/
def boundedAboveDerivedTensorRightUnitor (X : D) :
    (T).obj (X, boundedAboveDerivedTensorUnit) ≅ X :=
  ObjectProperty.isoMk _
    (boundedAboveDerivedTensorModelIso _ _ (boundedAboveDerivedChosenModel X)
      boundedAboveDerivedTensorUnitModel ≪≫
      DerivedCategory.Q.mapIso
        (cochainTensorRightUnitor (boundedAboveDerivedChosenModel X).complex) ≪≫
      (boundedAboveDerivedChosenModel X).iso)

lemma boundedAboveDerivedTensorLeftUnitor_naturality {X Y : D} (f : X ⟶ Y) :
    (T).map (𝟙 boundedAboveDerivedTensorUnit, f) ≫ (boundedAboveDerivedTensorLeftUnitor Y).hom =
      (boundedAboveDerivedTensorLeftUnitor X).hom ≫ f := by
  apply InducedCategory.hom_ext
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  have hn := boundedAboveDerivedTensorModelIso_naturality
    boundedAboveDerivedTensorUnitModel boundedAboveDerivedTensorUnitModel P Q
    (𝟙 boundedAboveDerivedTensorUnit) f (𝟙 cochainTensorUnit) (P.map Q f.hom)
    (by simp [boundedAboveDerivedTensorUnitModel]) (P.map_naturality Q f.hom)
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedAboveDerivedTensorLeftUnitor,
    ObjectProperty.isoMk, ObjectProperty.homMk_hom, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc]
  rw [← Category.assoc, hn, Category.assoc]
  rw [← Category.assoc (DerivedCategory.Q.map _), ← CategoryTheory.Functor.map_comp]
  have hu : cochainTensorMap (𝟙 cochainTensorUnit) (P.map Q f.hom) ≫
      (cochainTensorLeftUnitor Q.complex).hom =
      (cochainTensorLeftUnitor P.complex).hom ≫ P.map Q f.hom :=
    MonoidalCategory.leftUnitor_naturality _
  rw [hu, CategoryTheory.Functor.map_comp, Category.assoc, P.map_naturality Q f.hom]

lemma boundedAboveDerivedTensorRightUnitor_naturality {X Y : D} (f : X ⟶ Y) :
    (T).map (f, 𝟙 boundedAboveDerivedTensorUnit) ≫ (boundedAboveDerivedTensorRightUnitor Y).hom =
      (boundedAboveDerivedTensorRightUnitor X).hom ≫ f := by
  apply InducedCategory.hom_ext
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  have hn := boundedAboveDerivedTensorModelIso_naturality
    P Q boundedAboveDerivedTensorUnitModel boundedAboveDerivedTensorUnitModel
    f (𝟙 boundedAboveDerivedTensorUnit) (P.map Q f.hom) (𝟙 cochainTensorUnit)
    (P.map_naturality Q f.hom) (by simp [boundedAboveDerivedTensorUnitModel])
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedAboveDerivedTensorRightUnitor,
    ObjectProperty.isoMk, ObjectProperty.homMk_hom, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc]
  rw [← Category.assoc, hn, Category.assoc]
  rw [← Category.assoc (DerivedCategory.Q.map _), ← CategoryTheory.Functor.map_comp]
  have hu : cochainTensorMap (P.map Q f.hom) (𝟙 cochainTensorUnit) ≫
      (cochainTensorRightUnitor Q.complex).hom =
      (cochainTensorRightUnitor P.complex).hom ≫ P.map Q f.hom :=
    MonoidalCategory.rightUnitor_naturality _
  rw [hu, CategoryTheory.Functor.map_comp, Category.assoc, P.map_naturality Q f.hom]

end SerrePositivity
