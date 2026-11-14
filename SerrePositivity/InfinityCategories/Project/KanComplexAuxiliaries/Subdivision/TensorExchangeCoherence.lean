module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomTensorStrength

/-!
概要：対称テンソルの三因子交換と結合子の整合性。
方針：braiding の六角形と対称性で因子を揃え、結合子の coherence を用いる。
規約：通常の閉構造は不要。使われ方：内部 Hom の strength の交換式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.Spectra.HomTensorStrength
end SerrePositivity.KST.Spectra.HomTensorStrength
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.HomTensorStrength
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

lemma exchange_tensor_left (S X A E : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange (S ⊗ X) A E).hom ≫ A ◁ (α_ S X E).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A S (X ⊗ E)).hom =
      (α_ S X (A ⊗ E)).hom ≫ S ◁ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange X A E).hom := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, tensorRight,
    Functor.flip, curriedTensor, BraidedCategory.braiding_tensor_left_hom,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  have hm : (α_ A S X).hom ▷ E ≫ (α_ A (S ⊗ X) E).hom ≫
      A ◁ (α_ S X E).hom ≫ (α_ A S (X ⊗ E)).inv = (α_ (A ⊗ S) X E).hom := by
    monoidal
  have hmt := congrArg (fun f ↦ f ≫ (β_ A S).hom ▷ (X ⊗ E) ≫
    (α_ S A (X ⊗ E)).hom) hm
  simp only [Category.assoc] at hmt
  rw [hmt, associator_naturality_left_assoc,
    ← comp_whiskerRight_assoc (β_ S A).hom (β_ A S).hom (X ⊗ E),
    SymmetricCategory.symmetry, id_whiskerRight, Category.id_comp]
  monoidal

/-- 二つの左因子を続けて交換すると元に戻る。 -/
@[reassoc]
lemma exchange_involution (A P Q : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A P Q).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange P A Q).hom = 𝟙 _ := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, tensorRight, Functor.flip, curriedTensor, Category.assoc,
    Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc, SymmetricCategory.symmetry,
    id_whiskerRight, Category.id_comp, Iso.inv_hom_id]

/-- 左テンソルの中での交換と、二因子全体の交換の整合性。 -/
lemma exchange_tensor_left_reordered (X P A Q : C) :
    X ◁ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A P Q).hom ≫
        (α_ X P (A ⊗ Q)).inv ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange (X ⊗ P) A Q).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange X A (P ⊗ Q)).hom ≫ A ◁ (α_ X P Q).inv := by
  apply (cancel_mono (A ◁ (α_ X P Q).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A X (P ⊗ Q)).hom)).mp
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exchange_tensor_left]
  simp only [Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exchange_involution, whiskerLeft_id, Category.id_comp,
    Iso.inv_hom_id]
  rw [← whiskerLeft_comp, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exchange_involution, whiskerLeft_id]

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.HomTensorStrength.exchange_involution := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exchange_involution

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.HomTensorStrength.exchange_involution_assoc := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exchange_involution_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.HomTensorStrength.exchange_tensor_left := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exchange_tensor_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.HomTensorStrength.exchange_tensor_left_reordered := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exchange_tensor_left_reordered
