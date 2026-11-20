module


public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomTensorStrength

/-!
概要：内部 Hom とテンソルの strength のパラメータ自然性。
方針：因子交換の中央の変数の自然性と評価のテンソル交換を使う。
規約：閉 braided モノイダル圏の実際の射。使われ方：cotensor の豊穣自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.HomTensorStrength
end SerrePositivity.KST.Spectra.HomTensorStrength
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.HomTensorStrength
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- 三因子の最初の二因子の交換は、中央の因子の射について自然。 -/
@[reassoc]
lemma exchange_natural_middle (A : C) {P Q : C} (f : P ⟶ Q) (Z : C) :
    A ◁ (f ▷ Z) ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A Q Z).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A P Z).hom ≫ f ▷ (A ⊗ Z) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    tensorRight, Functor.flip, curriedTensor, Category.assoc]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_right, comp_whiskerRight_assoc,
    associator_naturality_left]

variable [MonoidalClosed C]
/-- strength はテンソルするパラメータの任意の射について自然。 -/
@[reassoc]
lemma natural_parameter {P Q : C} (f : P ⟶ Q) (A Y : C) :
    f ▷ (ihom A).obj Y ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map Q A Y =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map P A Y ≫ (ihom A).map (f ▷ Y) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_right]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map, uncurry_curry]
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exchange_natural_middle_assoc, ← whisker_exchange, Category.assoc]

/-- strength はパラメータと標的を同時に動かしても自然。 -/
@[reassoc]
lemma natural {P Q Y Z : C} (f : P ⟶ Q) (g : Y ⟶ Z) (A : C) :
    (f ⊗ₘ (ihom A).map g) ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map Q A Z =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map P A Y ≫ (ihom A).map (f ⊗ₘ g) := by
  rw [tensorHom_def, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.natural_post,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.natural_parameter, Category.assoc,
    ← Functor.map_comp, ← tensorHom_def]

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
