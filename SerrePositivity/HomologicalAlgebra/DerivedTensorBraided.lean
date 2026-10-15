module
public import SerrePositivity.HomologicalAlgebra.DerivedTensorSymmetry
public import SerrePositivity.HomologicalAlgebra.CochainTensorBraided

/-! # Hexagon compatibility of the actual bounded-above derived tensor -/
@[expose] public noncomputable section
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

/-- The signed cochain symmetry represents the actual derived symmetry in arbitrary models. -/
lemma boundedAboveSymmetryModel_map (X Y : D)
    (P : BoundedAboveDerivedModel X.obj) (Q : BoundedAboveDerivedModel Y.obj) :
    DerivedCategory.Q.map (cochainTensorSymmetry P.complex Q.complex).hom ≫
        (boundedAboveTensorModelOf Y X Q P).iso.hom =
      (boundedAboveTensorModelOf X Y P Q).iso.hom ≫
        (boundedAboveDerivedTensorSymmetry X Y).hom.hom := by
  change _ ≫ (boundedAboveDerivedTensorModelIso Y X Q P).inv =
    (boundedAboveDerivedTensorModelIso X Y P Q).inv ≫ _
  apply (cancel_mono (boundedAboveDerivedTensorModelIso Y X Q P).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [boundedAboveDerivedTensorSymmetry_models]
  simp only [Iso.inv_hom_id_assoc]

/-- The actual derived signed symmetry satisfies the first hexagon. -/
lemma boundedAboveDerivedTensorSymmetry_hexagon_forward (X Y Z : D) :
    (boundedAboveDerivedTensorAssociator X Y Z).hom ≫
        (boundedAboveDerivedTensorSymmetry X (Y ⊗ᴰ Z)).hom ≫
        (boundedAboveDerivedTensorAssociator Y Z X).hom =
      (T).map (CategoryTheory.Prod.mkHom (boundedAboveDerivedTensorSymmetry X Y).hom (𝟙 Z)) ≫
        (boundedAboveDerivedTensorAssociator Y X Z).hom ≫
        (T).map (CategoryTheory.Prod.mkHom (𝟙 Y) (boundedAboveDerivedTensorSymmetry X Z).hom) := by
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let V := boundedAboveDerivedChosenModel Z
  let XY := boundedAboveTensorModelOf X Y P Q
  let YZ := boundedAboveTensorModelOf Y Z Q V
  let YX := boundedAboveTensorModelOf Y X Q P
  let XZ := boundedAboveTensorModelOf X Z P V
  let ZX := boundedAboveTensorModelOf Z X V P
  let A := boundedAboveTensorModelOf (X ⊗ᴰ Y) Z XY V
  let B := boundedAboveTensorModelOf X (Y ⊗ᴰ Z) P YZ
  let C := boundedAboveTensorModelOf (Y ⊗ᴰ Z) X YZ P
  let F := boundedAboveTensorModelOf Y (Z ⊗ᴰ X) Q ZX
  let E := boundedAboveTensorModelOf (Y ⊗ᴰ X) Z YX V
  let G := boundedAboveTensorModelOf Y (X ⊗ᴰ Z) Q XZ
  let a₁ := (boundedAboveDerivedTensorAssociator X Y Z).hom
  let a₂ := (boundedAboveDerivedTensorSymmetry X (Y ⊗ᴰ Z)).hom
  let a₃ := (boundedAboveDerivedTensorAssociator Y Z X).hom
  let b₁ := (T).map (CategoryTheory.Prod.mkHom (boundedAboveDerivedTensorSymmetry X Y).hom (𝟙 Z))
  let b₂ := (boundedAboveDerivedTensorAssociator Y X Z).hom
  let b₃ := (T).map (CategoryTheory.Prod.mkHom (𝟙 Y) (boundedAboveDerivedTensorSymmetry X Z).hom)
  let c₁ : A.complex ⟶ B.complex :=
    (cochainTensorAssociator P.complex Q.complex V.complex).hom
  let c₂ : B.complex ⟶ C.complex :=
    (cochainTensorSymmetry P.complex (cochainTensor Q.complex V.complex)).hom
  let c₃ : C.complex ⟶ F.complex :=
    (cochainTensorAssociator Q.complex V.complex P.complex).hom
  let d₁ : A.complex ⟶ E.complex :=
    cochainTensorMap (cochainTensorSymmetry P.complex Q.complex).hom (𝟙 V.complex)
  let d₂ : E.complex ⟶ G.complex :=
    (cochainTensorAssociator Q.complex P.complex V.complex).hom
  let d₃ : G.complex ⟶ F.complex :=
    cochainTensorMap (𝟙 Q.complex) (cochainTensorSymmetry P.complex V.complex).hom
  have h₁ := boundedAboveAssociatorModel_map X Y Z P Q V
  have h₂ := boundedAboveSymmetryModel_map X (Y ⊗ᴰ Z) P YZ
  have h₃ := boundedAboveAssociatorModel_map Y Z X Q V P
  have h₄ := boundedAboveTensorModelOf_map
    (X := X ⊗ᴰ Y) (X' := Y ⊗ᴰ X) (Y := Z) (Y' := Z) XY YX V V
    (boundedAboveDerivedTensorSymmetry X Y).hom (𝟙 Z)
    (cochainTensorSymmetry P.complex Q.complex).hom (𝟙 V.complex)
    (boundedAboveSymmetryModel_map X Y P Q) (by simp)
  have h₅ := boundedAboveAssociatorModel_map Y X Z Q P V
  have h₆ := boundedAboveTensorModelOf_map
    (X := Y) (X' := Y) (Y := X ⊗ᴰ Z) (Y' := Z ⊗ᴰ X) Q Q XZ ZX
    (𝟙 Y) (boundedAboveDerivedTensorSymmetry X Z).hom (𝟙 Q.complex)
    (cochainTensorSymmetry P.complex V.complex).hom
    (by simp) (boundedAboveSymmetryModel_map X Z P V)
  have e₁ := boundedAboveDerivedMorphism_models
    (X := (X ⊗ᴰ Y) ⊗ᴰ Z) (Y := X ⊗ᴰ (Y ⊗ᴰ Z)) A B a₁ c₁ h₁
  have e₂ := boundedAboveDerivedMorphism_models
    (X := X ⊗ᴰ (Y ⊗ᴰ Z)) (Y := (Y ⊗ᴰ Z) ⊗ᴰ X) B C a₂ c₂ h₂
  have e₃ := boundedAboveDerivedMorphism_models
    (X := (Y ⊗ᴰ Z) ⊗ᴰ X) (Y := Y ⊗ᴰ (Z ⊗ᴰ X)) C F a₃ c₃ h₃
  have e₄ := boundedAboveDerivedMorphism_models
    (X := (X ⊗ᴰ Y) ⊗ᴰ Z) (Y := (Y ⊗ᴰ X) ⊗ᴰ Z) A E b₁ d₁ h₄
  have e₅ := boundedAboveDerivedMorphism_models
    (X := (Y ⊗ᴰ X) ⊗ᴰ Z) (Y := Y ⊗ᴰ (X ⊗ᴰ Z)) E G b₂ d₂ h₅
  have e₆ := boundedAboveDerivedMorphism_models
    (X := Y ⊗ᴰ (X ⊗ᴰ Z)) (Y := Y ⊗ᴰ (Z ⊗ᴰ X)) G F b₃ d₃ h₆
  change a₁ ≫ a₂ ≫ a₃ = b₁ ≫ b₂ ≫ b₃
  apply InducedCategory.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [e₁, e₂, e₃, e₄, e₅, e₆]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  apply congrArg (A.iso.inv ≫ ·)
  simp only [← Category.assoc]
  apply (cancel_mono F.iso.hom).mpr
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  apply congrArg DerivedCategory.Q.map
  exact cochainTensorSymmetry_hexagon_forward P.complex Q.complex V.complex

/-- Inverse derived factor exchange is the same exchange in reverse order. -/
@[simp]
lemma boundedAboveDerivedTensorSymmetry_inv (X Y : D) :
    (boundedAboveDerivedTensorSymmetry X Y).inv =
      (boundedAboveDerivedTensorSymmetry Y X).hom := by
  apply (cancel_epi (boundedAboveDerivedTensorSymmetry X Y).hom).mp
  rw [Iso.hom_inv_id, boundedAboveDerivedTensorSymmetry_hom_comp]

/-- The actual derived signed symmetry also satisfies the second hexagon. -/
lemma boundedAboveDerivedTensorSymmetry_hexagon_reverse (X Y Z : D) :
    (boundedAboveDerivedTensorAssociator X Y Z).inv ≫
        (boundedAboveDerivedTensorSymmetry (X ⊗ᴰ Y) Z).hom ≫
        (boundedAboveDerivedTensorAssociator Z X Y).inv =
      (T).map (CategoryTheory.Prod.mkHom (𝟙 X) (boundedAboveDerivedTensorSymmetry Y Z).hom) ≫
        (boundedAboveDerivedTensorAssociator X Z Y).inv ≫
        (T).map (CategoryTheory.Prod.mkHom (boundedAboveDerivedTensorSymmetry X Z).hom (𝟙 Y)) := by
  have h :
      boundedAboveDerivedTensorAssociator Z X Y ≪≫
          boundedAboveDerivedTensorSymmetry Z (X ⊗ᴰ Y) ≪≫
          boundedAboveDerivedTensorAssociator X Y Z =
        MonoidalCategory.tensorIso (boundedAboveDerivedTensorSymmetry Z X) (Iso.refl Y) ≪≫
          boundedAboveDerivedTensorAssociator X Z Y ≪≫
          MonoidalCategory.tensorIso (Iso.refl X) (boundedAboveDerivedTensorSymmetry Z Y) := by
    apply Iso.ext
    exact boundedAboveDerivedTensorSymmetry_hexagon_forward Z X Y
  have hi := congrArg Iso.inv h
  simp only [Iso.trans_inv, MonoidalCategory.tensorIso_inv, Iso.refl_inv,
    boundedAboveDerivedTensorSymmetry_inv, Category.assoc] at hi
  exact hi

/-- The previously constructed actual derived tensor is symmetric monoidal. -/
instance boundedAboveDerivedSymmetricCategory : SymmetricCategory D where
  braiding := boundedAboveDerivedTensorSymmetry
  braiding_naturality_right := by
    intro X Y Z f
    exact boundedAboveDerivedTensorSymmetry_naturality (𝟙 X) f
  braiding_naturality_left := by
    intro X Y f Z
    exact boundedAboveDerivedTensorSymmetry_naturality f (𝟙 Z)
  hexagon_forward := boundedAboveDerivedTensorSymmetry_hexagon_forward
  hexagon_reverse := boundedAboveDerivedTensorSymmetry_hexagon_reverse
  symmetry := boundedAboveDerivedTensorSymmetry_hom_comp

end SerrePositivity
