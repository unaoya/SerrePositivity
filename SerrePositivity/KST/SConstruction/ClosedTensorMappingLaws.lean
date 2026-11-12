module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping

/-! # 元の閉 Hom tensor 作用の通常射回収と左因子自然性
概要：同じ左 tensor の全写像対象への作用を、通常射と左因子の射について照合する。
方針：元の評価へ uncurry し、結合子と二因子の自然性を使う。
規約：一般の閉モノイダル圏の式。使われ方：点つき円柱の厳密豊穣関手。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- 元の tensor Hom 作用は、同じ元の通常射の左 tensor を回収する。 -/
lemma closedTensorMapping_curry' (K : C) {X Y : C} (f : X ⟶ Y) :
    curry' f ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map K X Y = curry' (K ◁ f) := by
  apply uncurry_injective
  rw [uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map, uncurry_curry]
  conv_rhs => rw [curry', uncurry_curry]
  change (K ⊗ X) ◁ curry' f ≫
    ((α_ K X ((ihom X).obj Y)).hom ≫ K ◁ ((ihom.ev X).app Y)) =
      (ρ_ (K ⊗ X)).hom ≫ K ◁ f
  rw [associator_naturality_right_assoc, ← whiskerLeft_comp,
    whiskerLeft_curry'_ihom_ev_app, whiskerLeft_comp, ← Category.assoc,
    ← rightUnitor_tensor_hom]

/-- 元の全 tensor Hom 作用は、同じ元の閉 Hom の恒等射を保つ。 -/
lemma closedTensorMapping_id (K X : C) :
    MonoidalClosed.id X ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map K X X = MonoidalClosed.id (K ⊗ X) := by
  simpa only [curry'_id, whiskerLeft_id] using closedTensorMapping_curry' K (𝟙 X)

/-- 同じ全 Hom の tensor 作用は、左因子の射についても厳密に自然。 -/
lemma closedTensorMapping_parameter {K L : C} (a : K ⟶ L) (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map K X Y ≫ (ihom (K ⊗ X)).map (a ▷ Y) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map L X Y ≫ (pre (a ▷ X)).app (L ⊗ Y) := by
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_pre_app, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map, uncurry_curry]
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map, uncurry_curry]
  erw [Category.assoc, whisker_exchange, ← Category.assoc,
    ← associator_naturality_left, Category.assoc]

end SerrePositivity.KST.SConstruction
