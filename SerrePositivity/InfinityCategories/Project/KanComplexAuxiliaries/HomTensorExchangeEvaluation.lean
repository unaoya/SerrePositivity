module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength

/-!
概要：右パラメータの作用と左パラメータの作用の評価の比較。
方針：braiding の六角形・対称性と評価射の自然性を使う。
規約：対称モノイダル圏の実際の射。使われ方：weighted end の作用の左右の順序の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.Spectra.HomTensorStrength
end SerrePositivity.KST.Spectra.HomTensorStrength
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.HomTensorStrength
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 左の二因子の交換を、右側へ動かす二つの braiding と結合子で表す。 -/
lemma exchange_left_form (W K E : C) :
    W ◁ (β_ K E).hom ≫ (α_ W E K).inv ≫ (β_ (W ⊗ E) K).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange W K E).hom := by
  rw [BraidedCategory.braiding_tensor_left_hom]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    tensorRight, Functor.flip, curriedTensor, Iso.inv_hom_id_assoc]
  rw [← whiskerLeft_comp_assoc, SymmetricCategory.symmetry, whiskerLeft_id, Category.id_comp]

/-- 右パラメータの評価を左へ交換した式は、三因子の交換による評価。 -/
lemma exchange_evaluation (W K E B : C) (g : W ⊗ E ⟶ B) :
    W ◁ (β_ K E).hom ≫ (α_ W E K).inv ≫ g ▷ K ≫ (β_ B K).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange W K E).hom ≫ K ◁ g := by
  rw [BraidedCategory.braiding_naturality_left]
  simpa only [Category.assoc] using
    congrArg (fun f ↦ f ≫ K ◁ g) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exchange_left_form W K E)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.HomTensorStrength.exchange_evaluation := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exchange_evaluation

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.HomTensorStrength.exchange_left_form := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exchange_left_form
