module
public import SerrePositivity.HomologicalAlgebra.DerivedTensorCoherenceModels

/-! # The triangle identity for derived tensor -/
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
local notation "U" => boundedAboveDerivedTensorUnit (R := R)

/-- Compute the actual derived left unitor in any projective representative. -/
lemma boundedAboveDerivedLeftUnitor_models (X : D) (P : BoundedAboveDerivedModel X.obj) :
    (boundedAboveDerivedTensorLeftUnitor X).hom.hom =
      (boundedAboveDerivedTensorModelIso (U) X boundedAboveDerivedTensorUnitModel P).hom ≫
        DerivedCategory.Q.map (cochainTensorLeftUnitor P.complex).hom ≫ P.iso.hom := by
  let A := boundedAboveDerivedChosenModel X
  have hn := boundedAboveDerivedTensorModelIso_naturality
    boundedAboveDerivedTensorUnitModel boundedAboveDerivedTensorUnitModel A P
    (𝟙 (U)) (𝟙 X) (𝟙 cochainTensorUnit) (A.map P (𝟙 X.obj))
    (by simp [boundedAboveDerivedTensorUnitModel]) (A.map_naturality P (𝟙 X.obj))
  have hi := (T).map_id ((U), X)
  simp only [CategoryTheory.prod_id'] at hi
  rw [hi, ObjectProperty.FullSubcategory.id_hom, Category.id_comp] at hn
  rw [hn]
  simp only [boundedAboveDerivedTensorLeftUnitor, ObjectProperty.isoMk, ObjectProperty.homMk_hom,
    Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  congr 1
  rw [← Category.assoc (DerivedCategory.Q.map _), ← CategoryTheory.Functor.map_comp]
  have hu : cochainTensorMap (𝟙 cochainTensorUnit) (A.map P (𝟙 X.obj)) ≫
      (cochainTensorLeftUnitor P.complex).hom =
      (cochainTensorLeftUnitor A.complex).hom ≫ A.map P (𝟙 X.obj) :=
    MonoidalCategory.leftUnitor_naturality _
  rw [hu, CategoryTheory.Functor.map_comp, Category.assoc, A.map_naturality P (𝟙 X.obj),
    Category.comp_id]

/-- Compute the actual derived right unitor in any projective representative. -/
lemma boundedAboveDerivedRightUnitor_models (X : D) (P : BoundedAboveDerivedModel X.obj) :
    (boundedAboveDerivedTensorRightUnitor X).hom.hom =
      (boundedAboveDerivedTensorModelIso X (U) P boundedAboveDerivedTensorUnitModel).hom ≫
        DerivedCategory.Q.map (cochainTensorRightUnitor P.complex).hom ≫ P.iso.hom := by
  let A := boundedAboveDerivedChosenModel X
  have hn := boundedAboveDerivedTensorModelIso_naturality
    A P boundedAboveDerivedTensorUnitModel boundedAboveDerivedTensorUnitModel
    (𝟙 X) (𝟙 (U)) (A.map P (𝟙 X.obj)) (𝟙 cochainTensorUnit)
    (A.map_naturality P (𝟙 X.obj)) (by simp [boundedAboveDerivedTensorUnitModel])
  have hi := (T).map_id (X, (U))
  simp only [CategoryTheory.prod_id'] at hi
  rw [hi, ObjectProperty.FullSubcategory.id_hom, Category.id_comp] at hn
  rw [hn]
  simp only [boundedAboveDerivedTensorRightUnitor, ObjectProperty.isoMk, ObjectProperty.homMk_hom,
    Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  congr 1
  rw [← Category.assoc (DerivedCategory.Q.map _), ← CategoryTheory.Functor.map_comp]
  have hu : cochainTensorMap (A.map P (𝟙 X.obj)) (𝟙 cochainTensorUnit) ≫
      (cochainTensorRightUnitor P.complex).hom =
      (cochainTensorRightUnitor A.complex).hom ≫ A.map P (𝟙 X.obj) :=
    MonoidalCategory.rightUnitor_naturality _
  rw [hu, CategoryTheory.Functor.map_comp, Category.assoc, A.map_naturality P (𝟙 X.obj),
    Category.comp_id]

/-- The derived associator and the standard unitors satisfy the triangle identity. -/
lemma boundedAboveDerivedTensor_triangle (X Y : D) :
    (boundedAboveDerivedTensorAssociator X (U) Y).hom ≫
        (T).map (CategoryTheory.Prod.mkHom (𝟙 X) (boundedAboveDerivedTensorLeftUnitor Y).hom) =
      (T).map (CategoryTheory.Prod.mkHom (boundedAboveDerivedTensorRightUnitor X).hom (𝟙 Y)) := by
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let W := boundedAboveDerivedTensorUnitModel (R := R)
  have hl : ((T).map (CategoryTheory.Prod.mkHom (𝟙 X)
        (boundedAboveDerivedTensorLeftUnitor Y).hom)).hom ≫
        (boundedAboveDerivedTensorModelIso X Y P Q).hom =
      (boundedAboveTensorRightModelIsoOf X (U) Y P W Q).hom ≫ DerivedCategory.Q.map
        (cochainTensorMap (𝟙 P.complex) (cochainTensorLeftUnitor Q.complex).hom) := by
    apply boundedAboveDerivedTensorModelIso_naturality P P
      (boundedAboveTensorModelOf (U) Y W Q) Q
    · simp
    · rw [boundedAboveDerivedLeftUnitor_models Y Q]
      change _ = (boundedAboveDerivedTensorModelIso (U) Y W Q).inv ≫
        ((boundedAboveDerivedTensorModelIso (U) Y W Q).hom ≫ _ ≫ _)
      simp only [Iso.inv_hom_id_assoc]
  have hr : ((T).map (CategoryTheory.Prod.mkHom
        (boundedAboveDerivedTensorRightUnitor X).hom (𝟙 Y))).hom ≫
        (boundedAboveDerivedTensorModelIso X Y P Q).hom =
      (boundedAboveTensorLeftModelIsoOf X (U) Y P W Q).hom ≫ DerivedCategory.Q.map
        (cochainTensorMap (cochainTensorRightUnitor P.complex).hom (𝟙 Q.complex)) := by
    apply boundedAboveDerivedTensorModelIso_naturality
      (boundedAboveTensorModelOf X (U) P W) P Q Q
    · rw [boundedAboveDerivedRightUnitor_models X P]
      change _ = (boundedAboveDerivedTensorModelIso X (U) P W).inv ≫
        ((boundedAboveDerivedTensorModelIso X (U) P W).hom ≫ _ ≫ _)
      simp only [Iso.inv_hom_id_assoc]
    · simp
  apply InducedCategory.hom_ext
  apply (cancel_mono (boundedAboveDerivedTensorModelIso X Y P Q).hom).mp
  simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
  rw [hl, ← Category.assoc, boundedAboveDerivedAssociator_models, hr, Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg DerivedCategory.Q.map (MonoidalCategory.triangle P.complex Q.complex)

end SerrePositivity
