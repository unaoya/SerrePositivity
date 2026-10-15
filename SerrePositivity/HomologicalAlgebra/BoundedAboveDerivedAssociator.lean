module
public import SerrePositivity.HomologicalAlgebra.CochainTensorProjective
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedTensor
public import Mathlib.CategoryTheory.Products.Associator

/-! # Associativity of the bounded-above derived tensor product -/
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

/-- Tensoring the chosen representatives gives a projective model of their derived tensor. -/
def boundedAboveDerivedTensorModel (X Y : D) : BoundedAboveDerivedModel ((T).obj (X, Y)).obj where
  complex := cochainTensor (boundedAboveDerivedChosenModel X).complex
    (boundedAboveDerivedChosenModel Y).complex
  bound := (boundedAboveDerivedChosenModel X).bound + (boundedAboveDerivedChosenModel Y).bound
  bounded := cochainTensor_isStrictlyLE _ _ _ _
  projective n := by
    have := cochainTensor_projective_X (boundedAboveDerivedChosenModel X).complex
      (boundedAboveDerivedChosenModel Y).complex (fun _ => by infer_instance)
      (fun _ => by infer_instance) n
    infer_instance
  iso := Iso.refl _

/-- Compute a left-associated derived triple tensor by the corresponding triple complex. -/
def boundedAboveDerivedTensorLeftModelIso (X Y Z : D) :
    ((T).obj ((T).obj (X, Y), Z)).obj ≅ DerivedCategory.Q.obj
      (cochainTensor (cochainTensor (boundedAboveDerivedChosenModel X).complex
        (boundedAboveDerivedChosenModel Y).complex) (boundedAboveDerivedChosenModel Z).complex) :=
  boundedAboveDerivedTensorModelIso _ _ (boundedAboveDerivedTensorModel X Y)
    (boundedAboveDerivedChosenModel Z)

/-- Compute a right-associated derived triple tensor by the corresponding triple complex. -/
def boundedAboveDerivedTensorRightModelIso (X Y Z : D) :
    ((T).obj (X, (T).obj (Y, Z))).obj ≅ DerivedCategory.Q.obj
      (cochainTensor (boundedAboveDerivedChosenModel X).complex
        (cochainTensor (boundedAboveDerivedChosenModel Y).complex
          (boundedAboveDerivedChosenModel Z).complex)) :=
  boundedAboveDerivedTensorModelIso _ _ (boundedAboveDerivedChosenModel X)
    (boundedAboveDerivedTensorModel Y Z)

/-- Associativity in the standard bounded-above derived category. -/
def boundedAboveDerivedTensorAssociator (X Y Z : D) :
    (T).obj ((T).obj (X, Y), Z) ≅ (T).obj (X, (T).obj (Y, Z)) :=
  ObjectProperty.isoMk _
    (boundedAboveDerivedTensorLeftModelIso X Y Z ≪≫ DerivedCategory.Q.mapIso
      (cochainTensorAssociator (boundedAboveDerivedChosenModel X).complex
        (boundedAboveDerivedChosenModel Y).complex (boundedAboveDerivedChosenModel Z).complex) ≪≫
      (boundedAboveDerivedTensorRightModelIso X Y Z).symm)

lemma boundedAboveDerivedTensorLeftModelIso_naturality
    {X X' Y Y' Z Z' : D} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    ((T).map ((T).map (f, g), h)).hom ≫ (boundedAboveDerivedTensorLeftModelIso X' Y' Z').hom =
      (boundedAboveDerivedTensorLeftModelIso X Y Z).hom ≫ DerivedCategory.Q.map
        (cochainTensorMap (cochainTensorMap
          ((boundedAboveDerivedChosenModel X).map (boundedAboveDerivedChosenModel X') f.hom)
          ((boundedAboveDerivedChosenModel Y).map (boundedAboveDerivedChosenModel Y') g.hom))
          ((boundedAboveDerivedChosenModel Z).map (boundedAboveDerivedChosenModel Z') h.hom)) := by
  apply boundedAboveDerivedTensorModelIso_naturality
    (boundedAboveDerivedTensorModel X Y) (boundedAboveDerivedTensorModel X' Y')
    (boundedAboveDerivedChosenModel Z) (boundedAboveDerivedChosenModel Z')
  · change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp
    rfl
  · exact BoundedAboveDerivedModel.map_naturality _ _ h.hom

lemma boundedAboveDerivedTensorRightModelIso_naturality
    {X X' Y Y' Z Z' : D} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    ((T).map (f, (T).map (g, h))).hom ≫ (boundedAboveDerivedTensorRightModelIso X' Y' Z').hom =
      (boundedAboveDerivedTensorRightModelIso X Y Z).hom ≫ DerivedCategory.Q.map
        (cochainTensorMap
          ((boundedAboveDerivedChosenModel X).map (boundedAboveDerivedChosenModel X') f.hom)
          (cochainTensorMap
            ((boundedAboveDerivedChosenModel Y).map (boundedAboveDerivedChosenModel Y') g.hom)
            ((boundedAboveDerivedChosenModel Z).map
              (boundedAboveDerivedChosenModel Z') h.hom))) := by
  apply boundedAboveDerivedTensorModelIso_naturality
    (boundedAboveDerivedChosenModel X) (boundedAboveDerivedChosenModel X')
    (boundedAboveDerivedTensorModel Y Z) (boundedAboveDerivedTensorModel Y' Z')
  · exact BoundedAboveDerivedModel.map_naturality _ _ f.hom
  · change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp
    rfl

/-- The derived associator is natural in all three derived variables. -/
lemma boundedAboveDerivedTensorAssociator_naturality
    {X X' Y Y' Z Z' : D} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (T).map ((T).map (f, g), h) ≫ (boundedAboveDerivedTensorAssociator X' Y' Z').hom =
      (boundedAboveDerivedTensorAssociator X Y Z).hom ≫ (T).map (f, (T).map (g, h)) := by
  apply InducedCategory.hom_ext
  apply (cancel_mono (boundedAboveDerivedTensorRightModelIso X' Y' Z').hom).mp
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedAboveDerivedTensorAssociator,
    ObjectProperty.isoMk, ObjectProperty.homMk_hom, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [boundedAboveDerivedTensorRightModelIso_naturality f g h]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, boundedAboveDerivedTensorLeftModelIso_naturality f g h,
    Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  apply congrArg DerivedCategory.Q.map
  exact MonoidalCategory.associator_naturality _ _ _

/-- The two parenthesizations of the three-variable tensor functor are naturally isomorphic. -/
def boundedAboveDerivedTensorAssociatorNatIso :
    ((T).prod (𝟭 D)) ⋙ (T) ≅
      prod.associator D D D ⋙ ((𝟭 D).prod (T)) ⋙ (T) :=
  NatIso.ofComponents (fun X => boundedAboveDerivedTensorAssociator X.1.1 X.1.2 X.2)
    (fun f => boundedAboveDerivedTensorAssociator_naturality f.1.1 f.1.2 f.2)

end SerrePositivity
