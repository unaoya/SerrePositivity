module
public import SerrePositivity.HomologicalAlgebra.DerivedTensorTriangle

/-! # The pentagon identity for the standard bounded-above derived tensor -/
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
local infixr:70 " ⊗ᴰ " =>
  fun X Y : D => Functor.obj (boundedAboveDerivedTensor (R := R)) (X, Y)

set_option maxHeartbeats 600000 in
/-- The derived associator satisfies the pentagon on arbitrary bounded-above derived objects. -/
lemma boundedAboveDerivedTensor_pentagon (W X Y Z : D) :
    (T).map (CategoryTheory.Prod.mkHom (boundedAboveDerivedTensorAssociator W X Y).hom (𝟙 Z)) ≫
        (boundedAboveDerivedTensorAssociator W (X ⊗ᴰ Y) Z).hom ≫
        (T).map (CategoryTheory.Prod.mkHom (𝟙 W) (boundedAboveDerivedTensorAssociator X Y Z).hom) =
      (boundedAboveDerivedTensorAssociator (W ⊗ᴰ X) Y Z).hom ≫
        (boundedAboveDerivedTensorAssociator W X (Y ⊗ᴰ Z)).hom := by
  let P := boundedAboveDerivedChosenModel W
  let Q := boundedAboveDerivedChosenModel X
  let V := boundedAboveDerivedChosenModel Y
  let N := boundedAboveDerivedChosenModel Z
  let WX := boundedAboveTensorModelOf W X P Q
  let XY := boundedAboveTensorModelOf X Y Q V
  let YZ := boundedAboveTensorModelOf Y Z V N
  let WXYl := boundedAboveTensorModelOf (W ⊗ᴰ X) Y WX V
  let WXYr := boundedAboveTensorModelOf W (X ⊗ᴰ Y) P XY
  let XYZl := boundedAboveTensorModelOf (X ⊗ᴰ Y) Z XY N
  let XYZr := boundedAboveTensorModelOf X (Y ⊗ᴰ Z) Q YZ
  let A := boundedAboveTensorModelOf ((W ⊗ᴰ X) ⊗ᴰ Y) Z WXYl N
  let B := boundedAboveTensorModelOf (W ⊗ᴰ (X ⊗ᴰ Y)) Z WXYr N
  let C := boundedAboveTensorModelOf W ((X ⊗ᴰ Y) ⊗ᴰ Z) P XYZl
  let F := boundedAboveTensorModelOf W (X ⊗ᴰ (Y ⊗ᴰ Z)) P XYZr
  let E := boundedAboveTensorModelOf (W ⊗ᴰ X) (Y ⊗ᴰ Z) WX YZ
  let a₁ := (T).map
    (CategoryTheory.Prod.mkHom (boundedAboveDerivedTensorAssociator W X Y).hom (𝟙 Z))
  let a₂ := (boundedAboveDerivedTensorAssociator W (X ⊗ᴰ Y) Z).hom
  let a₃ := (T).map
    (CategoryTheory.Prod.mkHom (𝟙 W) (boundedAboveDerivedTensorAssociator X Y Z).hom)
  let b₁ := (boundedAboveDerivedTensorAssociator (W ⊗ᴰ X) Y Z).hom
  let b₂ := (boundedAboveDerivedTensorAssociator W X (Y ⊗ᴰ Z)).hom
  let c₁ : A.complex ⟶ B.complex :=
    cochainTensorMap (cochainTensorAssociator P.complex Q.complex V.complex).hom (𝟙 N.complex)
  let c₂ : B.complex ⟶ C.complex :=
    (cochainTensorAssociator P.complex (cochainTensor Q.complex V.complex) N.complex).hom
  let c₃ : C.complex ⟶ F.complex :=
    cochainTensorMap (𝟙 P.complex) (cochainTensorAssociator Q.complex V.complex N.complex).hom
  let d₁ : A.complex ⟶ E.complex :=
    (cochainTensorAssociator (cochainTensor P.complex Q.complex) V.complex N.complex).hom
  let d₂ : E.complex ⟶ F.complex :=
    (cochainTensorAssociator P.complex Q.complex (cochainTensor V.complex N.complex)).hom
  have h₁ := boundedAboveTensorModelOf_map
    (X := (W ⊗ᴰ X) ⊗ᴰ Y) (X' := W ⊗ᴰ (X ⊗ᴰ Y)) (Y := Z) (Y' := Z) WXYl WXYr N N
    (boundedAboveDerivedTensorAssociator W X Y).hom (𝟙 Z)
    (cochainTensorAssociator P.complex Q.complex V.complex).hom (𝟙 N.complex)
    (boundedAboveAssociatorModel_map W X Y P Q V) (by simp)
  have h₂ := boundedAboveAssociatorModel_map W (X ⊗ᴰ Y) Z P XY N
  have h₃ := boundedAboveTensorModelOf_map
    (X := W) (X' := W) (Y := (X ⊗ᴰ Y) ⊗ᴰ Z) (Y' := X ⊗ᴰ (Y ⊗ᴰ Z)) P P XYZl XYZr
    (𝟙 W) (boundedAboveDerivedTensorAssociator X Y Z).hom (𝟙 P.complex)
    (cochainTensorAssociator Q.complex V.complex N.complex).hom
    (by simp) (boundedAboveAssociatorModel_map X Y Z Q V N)
  have h₄ := boundedAboveAssociatorModel_map (W ⊗ᴰ X) Y Z WX V N
  have h₅ := boundedAboveAssociatorModel_map W X (Y ⊗ᴰ Z) P Q YZ
  have e₁ := boundedAboveDerivedMorphism_models
    (X := ((W ⊗ᴰ X) ⊗ᴰ Y) ⊗ᴰ Z) (Y := (W ⊗ᴰ (X ⊗ᴰ Y)) ⊗ᴰ Z) A B a₁ c₁ h₁
  have e₂ := boundedAboveDerivedMorphism_models
    (X := (W ⊗ᴰ (X ⊗ᴰ Y)) ⊗ᴰ Z) (Y := W ⊗ᴰ ((X ⊗ᴰ Y) ⊗ᴰ Z)) B C a₂ c₂ h₂
  have e₃ := boundedAboveDerivedMorphism_models
    (X := W ⊗ᴰ ((X ⊗ᴰ Y) ⊗ᴰ Z)) (Y := W ⊗ᴰ (X ⊗ᴰ (Y ⊗ᴰ Z))) C F a₃ c₃ h₃
  have e₄ := boundedAboveDerivedMorphism_models
    (X := ((W ⊗ᴰ X) ⊗ᴰ Y) ⊗ᴰ Z) (Y := (W ⊗ᴰ X) ⊗ᴰ (Y ⊗ᴰ Z)) A E b₁ d₁ h₄
  have e₅ := boundedAboveDerivedMorphism_models
    (X := (W ⊗ᴰ X) ⊗ᴰ (Y ⊗ᴰ Z)) (Y := W ⊗ᴰ (X ⊗ᴰ (Y ⊗ᴰ Z))) E F b₂ d₂ h₅
  change a₁ ≫ a₂ ≫ a₃ = b₁ ≫ b₂
  apply InducedCategory.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [e₁, e₂, e₃, e₄, e₅]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  congr 1
  simp only [← Category.assoc]
  apply (cancel_mono F.iso.hom).mpr
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp]
  apply congrArg DerivedCategory.Q.map
  dsimp only [c₁, c₂, c₃, d₁, d₂, A, B, C, E, F, WXYl, WXYr, XYZl, XYZr,
    WX, XY, YZ, boundedAboveTensorModelOf]
  change ((α_ P.complex Q.complex V.complex).hom ▷ N.complex ≫
      (α_ P.complex (Q.complex ⊗ V.complex) N.complex).hom) ≫
      P.complex ◁ (α_ Q.complex V.complex N.complex).hom =
    (α_ (P.complex ⊗ Q.complex) V.complex N.complex).hom ≫
      (α_ P.complex Q.complex (V.complex ⊗ N.complex)).hom
  simpa only [Category.assoc] using
    (MonoidalCategory.pentagon P.complex Q.complex V.complex N.complex)

end SerrePositivity
