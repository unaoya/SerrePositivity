module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomologicalAlgebra.DerivedTensorPentagon

/-! # Monoidal structure on the standard bounded-above derived category -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]
local notation "D" => DerivedCategory.Minus (ModuleCat R)
local notation "T" => boundedAboveDerivedTensor (R := R)

/-- Use precisely the tensor functor, unit, associator and unitors already constructed. -/
instance boundedAboveDerivedMonoidalStruct : MonoidalCategoryStruct D where
  tensorObj X Y := (T).obj (X, Y)
  tensorHom f g := (T).map (CategoryTheory.Prod.mkHom f g)
  whiskerLeft X _ _ f := (T).map (CategoryTheory.Prod.mkHom (𝟙 X) f)
  whiskerRight {_ _} f Y := (T).map (CategoryTheory.Prod.mkHom f (𝟙 Y))
  tensorUnit := boundedAboveDerivedTensorUnit
  associator := boundedAboveDerivedTensorAssociator
  leftUnitor := boundedAboveDerivedTensorLeftUnitor
  rightUnitor := boundedAboveDerivedTensorRightUnitor

/-- All monoidal laws, including the triangle and pentagon, hold for this actual derived tensor. -/
instance boundedAboveDerivedMonoidal : MonoidalCategory D where
  toMonoidalCategoryStruct := boundedAboveDerivedMonoidalStruct
  tensorHom_def f g := by
    change (T).map (CategoryTheory.Prod.mkHom f g) =
      (T).map (CategoryTheory.Prod.mkHom f (𝟙 _)) ≫
        (T).map (CategoryTheory.Prod.mkHom (𝟙 _) g)
    rw [← CategoryTheory.Functor.map_comp]
    apply (T).congr_map
    apply Prod.ext <;> simp
  id_tensorHom_id X Y := by
    change (T).map (CategoryTheory.Prod.mkHom (𝟙 X) (𝟙 Y)) = 𝟙 _
    simpa only [CategoryTheory.prod_id'] using (T).map_id (X, Y)
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := by
    change (T).map (CategoryTheory.Prod.mkHom f₁ f₂) ≫
      (T).map (CategoryTheory.Prod.mkHom g₁ g₂) =
        (T).map (CategoryTheory.Prod.mkHom (f₁ ≫ g₁) (f₂ ≫ g₂))
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  whiskerLeft_id X Y := by
    change (T).map (CategoryTheory.Prod.mkHom (𝟙 X) (𝟙 Y)) = 𝟙 _
    simpa only [CategoryTheory.prod_id'] using (T).map_id (X, Y)
  id_whiskerRight X Y := by
    change (T).map (CategoryTheory.Prod.mkHom (𝟙 X) (𝟙 Y)) = 𝟙 _
    simpa only [CategoryTheory.prod_id'] using (T).map_id (X, Y)
  associator_naturality f g h := boundedAboveDerivedTensorAssociator_naturality f g h
  leftUnitor_naturality f := boundedAboveDerivedTensorLeftUnitor_naturality f
  rightUnitor_naturality f := boundedAboveDerivedTensorRightUnitor_naturality f
  pentagon W X Y Z := boundedAboveDerivedTensor_pentagon W X Y Z
  triangle X Y := boundedAboveDerivedTensor_triangle X Y

end SerrePositivity

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.1.2.12" (partial := component) "仮定：可換環 R の通常の有界上導来圏（Lean が強い：有界上の通常圏の場合）。結論：既存の導来テンソルに単位・結合子を与え三角式と五角式を満たすモノイダル構造を構成する（導来テンソルのモノイダル構造の部分に一致）。全非有界 ∞ 圏上の対称モノイダル構造と cofibrant 局所化による一意性は含まれない。"] _root_.SerrePositivity.boundedAboveDerivedMonoidal
