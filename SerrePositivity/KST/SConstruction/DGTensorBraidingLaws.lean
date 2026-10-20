module
public import SerrePositivity.KST.SConstruction.DGTensorAssociatorLaws

/-! # tensor dg 交換関手に使う抽象 symmetric の式
概要：元の単位と二つの合成写像の交換を、抽象対称 monoidal 基底で照合する。
方針：braiding の自然性・hexagon・対称性から tensorμ との交換を得る。
規約：具体的複体の大きい構成を展開しない。使われ方：元の signed dg 交換関手。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable {V : Type u} [Category V] [MonoidalCategory V] [SymmetricCategory V]

/-- 元の二つの閉単位を tensor で挿入すると、signed 交換後の単位を回収する。 -/
lemma dgTensorBraiding_unit {X Y : V} (a : 𝟙_ V ⟶ X) (b : 𝟙_ V ⟶ Y) :
    (λ_ (𝟙_ V)).inv ≫ (a ⊗ₘ b) ≫ (β_ X Y).hom =
      (λ_ (𝟙_ V)).inv ≫ (b ⊗ₘ a) := by
  rw [BraidedCategory.braiding_naturality, ← Category.assoc, leftUnitor_inv_braiding]
  congr 1
  monoidal

/-- tensorμ と元の二つの合成写像は、同じ signed 交換と両立する。 -/
lemma dgTensorBraiding_composition {W X Y Z U T : V}
    (f : W ⊗ Y ⟶ U) (g : X ⊗ Z ⟶ T) :
    tensorμ W X Y Z ≫ (f ⊗ₘ g) ≫ (β_ U T).hom =
      ((β_ W X).hom ⊗ₘ (β_ Y Z).hom) ≫ tensorμ X W Z Y ≫ (g ⊗ₘ f) := by
  simp only [tensorμ, Category.assoc, BraidedCategory.braiding_naturality,
    BraidedCategory.braiding_tensor_right_hom, BraidedCategory.braiding_tensor_left_hom,
    comp_whiskerRight, whisker_assoc, whiskerLeft_comp, pentagon_assoc,
    pentagon_inv_hom_hom_hom_inv_assoc, Iso.inv_hom_id_assoc, whiskerLeft_hom_inv_assoc]
  slice_lhs 3 4 =>
    rw [← whiskerLeft_comp, ← comp_whiskerRight, SymmetricCategory.symmetry]
  simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.assoc, pentagon_inv_assoc,
    Iso.hom_inv_id_assoc]
  slice_lhs 1 2 => rw [← associator_inv_naturality_left]
  slice_lhs 2 3 => rw [Iso.inv_hom_id]
  rw [Category.id_comp]
  slice_lhs 2 3 => rw [← associator_naturality_right]
  slice_lhs 1 2 => rw [← tensorHom_def]
  simp only [Category.assoc]

end SerrePositivity.KST.SConstruction
