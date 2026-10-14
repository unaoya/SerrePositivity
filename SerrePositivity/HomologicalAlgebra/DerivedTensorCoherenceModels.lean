module
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedUnit

/-! # Arbitrary projective models for coherence of derived tensor -/
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

/-- Any two projective representatives give a projective representative of the derived tensor. -/
def boundedAboveTensorModelOf (X Y : D)
    (P : BoundedAboveDerivedModel X.obj) (Q : BoundedAboveDerivedModel Y.obj) :
    BoundedAboveDerivedModel ((T).obj (X, Y)).obj where
  complex := cochainTensor P.complex Q.complex
  bound := P.bound + Q.bound
  bounded := cochainTensor_isStrictlyLE _ _ _ _
  projective n := by
    have := cochainTensor_projective_X P.complex Q.complex
      (fun _ => by infer_instance) (fun _ => by infer_instance) n
    infer_instance
  iso := (boundedAboveDerivedTensorModelIso X Y P Q).symm

/-- Left-associated computation using three arbitrary projective models. -/
def boundedAboveTensorLeftModelIsoOf (X Y Z : D)
    (P : BoundedAboveDerivedModel X.obj) (Q : BoundedAboveDerivedModel Y.obj)
    (V : BoundedAboveDerivedModel Z.obj) :
    ((T).obj ((T).obj (X, Y), Z)).obj ≅
      DerivedCategory.Q.obj (cochainTensor (cochainTensor P.complex Q.complex) V.complex) :=
  boundedAboveDerivedTensorModelIso _ _ (boundedAboveTensorModelOf X Y P Q) V

/-- Right-associated computation using three arbitrary projective models. -/
def boundedAboveTensorRightModelIsoOf (X Y Z : D)
    (P : BoundedAboveDerivedModel X.obj) (Q : BoundedAboveDerivedModel Y.obj)
    (V : BoundedAboveDerivedModel Z.obj) :
    ((T).obj (X, (T).obj (Y, Z))).obj ≅
      DerivedCategory.Q.obj (cochainTensor P.complex (cochainTensor Q.complex V.complex)) :=
  boundedAboveDerivedTensorModelIso _ _ P (boundedAboveTensorModelOf Y Z Q V)

lemma boundedAboveTensorLeftModelIsoOf_hom (X Y Z : D)
    (P : BoundedAboveDerivedModel X.obj) (Q : BoundedAboveDerivedModel Y.obj)
    (V : BoundedAboveDerivedModel Z.obj) :
    (boundedAboveTensorLeftModelIsoOf X Y Z P Q V).hom =
      (boundedAboveDerivedTensorLeftModelIso X Y Z).hom ≫ DerivedCategory.Q.map (cochainTensorMap
        (cochainTensorMap ((boundedAboveDerivedChosenModel X).map P (𝟙 X.obj))
          ((boundedAboveDerivedChosenModel Y).map Q (𝟙 Y.obj)))
        ((boundedAboveDerivedChosenModel Z).map V (𝟙 Z.obj))) := by
  let A := boundedAboveDerivedChosenModel X
  let B := boundedAboveDerivedChosenModel Y
  let C := boundedAboveDerivedChosenModel Z
  have hh : DerivedCategory.Q.map (cochainTensorMap (A.map P (𝟙 X.obj)) (B.map Q (𝟙 Y.obj))) ≫
      (boundedAboveTensorModelOf X Y P Q).iso.hom =
      (boundedAboveDerivedTensorModel X Y).iso.hom ≫ 𝟙 ((T).obj (X, Y)).obj := by
    change (boundedAboveDerivedTensorModelIso X Y P Q).hom ≫
      (boundedAboveDerivedTensorModelIso X Y P Q).inv = 𝟙 _ ≫ 𝟙 _
    simp
  have hn := boundedAboveDerivedTensorModelIso_naturality
    (boundedAboveDerivedTensorModel X Y) (boundedAboveTensorModelOf X Y P Q) C V
    (𝟙 ((T).obj (X, Y))) (𝟙 Z)
    (cochainTensorMap (A.map P (𝟙 X.obj)) (B.map Q (𝟙 Y.obj))) (C.map V (𝟙 Z.obj))
    hh (C.map_naturality V (𝟙 Z.obj))
  have hi := (T).map_id ((T).obj (X, Y), Z)
  simp only [CategoryTheory.prod_id'] at hi
  rw [hi, ObjectProperty.FullSubcategory.id_hom, Category.id_comp] at hn
  exact hn

lemma boundedAboveTensorRightModelIsoOf_hom (X Y Z : D)
    (P : BoundedAboveDerivedModel X.obj) (Q : BoundedAboveDerivedModel Y.obj)
    (V : BoundedAboveDerivedModel Z.obj) :
    (boundedAboveTensorRightModelIsoOf X Y Z P Q V).hom =
      (boundedAboveDerivedTensorRightModelIso X Y Z).hom ≫ DerivedCategory.Q.map (cochainTensorMap
        ((boundedAboveDerivedChosenModel X).map P (𝟙 X.obj))
        (cochainTensorMap ((boundedAboveDerivedChosenModel Y).map Q (𝟙 Y.obj))
          ((boundedAboveDerivedChosenModel Z).map V (𝟙 Z.obj)))) := by
  let A := boundedAboveDerivedChosenModel X
  let B := boundedAboveDerivedChosenModel Y
  let C := boundedAboveDerivedChosenModel Z
  have hh : DerivedCategory.Q.map (cochainTensorMap (B.map Q (𝟙 Y.obj)) (C.map V (𝟙 Z.obj))) ≫
      (boundedAboveTensorModelOf Y Z Q V).iso.hom =
      (boundedAboveDerivedTensorModel Y Z).iso.hom ≫ 𝟙 ((T).obj (Y, Z)).obj := by
    change (boundedAboveDerivedTensorModelIso Y Z Q V).hom ≫
      (boundedAboveDerivedTensorModelIso Y Z Q V).inv = 𝟙 _ ≫ 𝟙 _
    simp
  have hn := boundedAboveDerivedTensorModelIso_naturality
    A P (boundedAboveDerivedTensorModel Y Z) (boundedAboveTensorModelOf Y Z Q V)
    (𝟙 X) (𝟙 ((T).obj (Y, Z)))
    (A.map P (𝟙 X.obj)) (cochainTensorMap (B.map Q (𝟙 Y.obj)) (C.map V (𝟙 Z.obj)))
    (A.map_naturality P (𝟙 X.obj)) hh
  have hi := (T).map_id (X, (T).obj (Y, Z))
  simp only [CategoryTheory.prod_id'] at hi
  rw [hi, ObjectProperty.FullSubcategory.id_hom, Category.id_comp] at hn
  exact hn

/-- The actual derived associator agrees with the ordinary associator in any projective models. -/
lemma boundedAboveDerivedAssociator_models (X Y Z : D)
    (P : BoundedAboveDerivedModel X.obj) (Q : BoundedAboveDerivedModel Y.obj)
    (V : BoundedAboveDerivedModel Z.obj) :
    (boundedAboveDerivedTensorAssociator X Y Z).hom.hom ≫
        (boundedAboveTensorRightModelIsoOf X Y Z P Q V).hom =
      (boundedAboveTensorLeftModelIsoOf X Y Z P Q V).hom ≫
        DerivedCategory.Q.map (cochainTensorAssociator P.complex Q.complex V.complex).hom := by
  rw [boundedAboveTensorLeftModelIsoOf_hom, boundedAboveTensorRightModelIsoOf_hom]
  simp only [boundedAboveDerivedTensorAssociator, ObjectProperty.isoMk, ObjectProperty.homMk_hom,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg DerivedCategory.Q.map (MonoidalCategory.associator_naturality _ _ _).symm

/-- A tensor of representing chain maps represents the tensor of the derived morphisms. -/
lemma boundedAboveTensorModelOf_map
    {X X' Y Y' : D} (P : BoundedAboveDerivedModel X.obj) (P' : BoundedAboveDerivedModel X'.obj)
    (Q : BoundedAboveDerivedModel Y.obj) (Q' : BoundedAboveDerivedModel Y'.obj)
    (f : X ⟶ X') (g : Y ⟶ Y') (h : P.complex ⟶ P'.complex) (k : Q.complex ⟶ Q'.complex)
    (hh : DerivedCategory.Q.map h ≫ P'.iso.hom = P.iso.hom ≫ f.hom)
    (hk : DerivedCategory.Q.map k ≫ Q'.iso.hom = Q.iso.hom ≫ g.hom) :
    DerivedCategory.Q.map (cochainTensorMap h k) ≫ (boundedAboveTensorModelOf X' Y' P' Q').iso.hom =
      (boundedAboveTensorModelOf X Y P Q).iso.hom ≫ ((T).map (f, g)).hom := by
  change _ ≫ (boundedAboveDerivedTensorModelIso X' Y' P' Q').inv =
    (boundedAboveDerivedTensorModelIso X Y P Q).inv ≫ _
  apply (cancel_mono (boundedAboveDerivedTensorModelIso X' Y' P' Q').hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [boundedAboveDerivedTensorModelIso_naturality P P' Q Q' f g h k hh hk]
  simp only [Iso.inv_hom_id_assoc]

/-- The ordinary associator represents the actual derived associator in the nested models. -/
lemma boundedAboveAssociatorModel_map (X Y Z : D)
    (P : BoundedAboveDerivedModel X.obj) (Q : BoundedAboveDerivedModel Y.obj)
    (V : BoundedAboveDerivedModel Z.obj) :
    DerivedCategory.Q.map (cochainTensorAssociator P.complex Q.complex V.complex).hom ≫
        (boundedAboveTensorModelOf X ((T).obj (Y, Z)) P
          (boundedAboveTensorModelOf Y Z Q V)).iso.hom =
      (boundedAboveTensorModelOf ((T).obj (X, Y)) Z
        (boundedAboveTensorModelOf X Y P Q) V).iso.hom ≫
        (boundedAboveDerivedTensorAssociator X Y Z).hom.hom := by
  change _ ≫ (boundedAboveTensorRightModelIsoOf X Y Z P Q V).inv =
    (boundedAboveTensorLeftModelIsoOf X Y Z P Q V).inv ≫ _
  apply (cancel_mono (boundedAboveTensorRightModelIsoOf X Y Z P Q V).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [boundedAboveDerivedAssociator_models]
  simp only [Iso.inv_hom_id_assoc]

/-- Recover a derived morphism from its chain representative and the model isomorphisms. -/
lemma boundedAboveDerivedMorphism_models {X Y : D}
    (P : BoundedAboveDerivedModel X.obj) (Q : BoundedAboveDerivedModel Y.obj)
    (f : X ⟶ Y) (h : P.complex ⟶ Q.complex)
    (hh : DerivedCategory.Q.map h ≫ Q.iso.hom = P.iso.hom ≫ f.hom) :
    f.hom = P.iso.inv ≫ DerivedCategory.Q.map h ≫ Q.iso.hom := by
  apply (cancel_epi P.iso.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  exact hh.symm

end SerrePositivity
