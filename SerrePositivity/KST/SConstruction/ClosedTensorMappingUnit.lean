module
public import SerrePositivity.KST.SConstruction.ClosedTensorMappingLaws

/-! # 左単位子と全 tensor 写像対象の厳密な可換性
概要：単位対象との左 tensor の全 Hom 作用を、元の左単位同型と照合する。
方針：元の評価へ uncurry し、左単位子の自然性と tensor の式を使う。
規約：通常射への制限を使わない。使われ方：点つき円柱の両端と射影。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- 左単位子は、単位対象との tensor の全 Hom 作用に自然。 -/
lemma closedTensorMapping_leftUnitor (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map (𝟙_ C) X Y ≫ (ihom ((𝟙_ C) ⊗ X)).map (λ_ Y).hom =
      (pre (λ_ X).hom).app Y := by
  apply uncurry_injective
  rw [uncurry_natural_right, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map, uncurry_curry, uncurry_pre]
  rw [Category.assoc, leftUnitor_naturality, leftUnitor_tensor_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- 逆左単位子も、同じ全 Hom 作用に自然。 -/
lemma closedTensorMapping_leftUnitor_inv (X Y : C) :
    (ihom X).map (λ_ Y).inv =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map (𝟙_ C) X Y ≫ (pre (λ_ X).inv).app ((𝟙_ C) ⊗ Y) := by
  apply uncurry_injective
  rw [uncurry_ihom_map, uncurry_pre_app, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map, uncurry_curry]
  erw [leftUnitor_inv_naturality, leftUnitor_tensor_inv, Category.assoc]

end SerrePositivity.KST.SConstruction
