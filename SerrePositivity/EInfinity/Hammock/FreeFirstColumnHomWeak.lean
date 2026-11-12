module

public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnObjects
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramVertexHomMap

/-!
# 元の自由解像の二方向比較の底の Hom の弱同値性

概要：元の二方向図式の底の固定 Hom 比較射自身が弱同値である。
方針：元の選択対象の native 指定 Hom augmentation との同型の正方形を使う。
規約：底の Hom の弱同値性を仮定せず、元の射への一致で証明する。
使われ方：DK10.4–10.6の底の弱比較の具体的な入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory SimplicialLocalization SerrePositivity.InfinityCategories
open TwoSidedDiagram.FixedVertices
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C.category)
def freeFirstTargetObjectEquiv (n : SimplexCategoryᵒᵖ) : C.category ≃
    (((Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardData C w X Y)).obj n).base :=
  markedObjectEquiv C
lemma freeFirstTargetObjectEquiv_naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (Z : C.category) :
    ((((Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardData C w X Y)).map θ).base.obj
      (freeFirstTargetObjectEquiv C w X Y n Z)) = freeFirstTargetObjectEquiv C w X Y m Z := rfl

def freeFirstSourceHomIso (U V : C.category) :
    homSpace (freeForwardForwardDiagram C w X Y) (freeFirstMarkedObjectEquiv C)
      (freeFirstMarkedObjectEquiv_naturality C w X Y) U V ≅
        freeResolutionCanonicalMarkedHom C U V :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

def freeFirstTargetHomIso (U V : C.category) :
    homSpace ((Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardData C w X Y))
      (freeFirstTargetObjectEquiv C w X Y) (freeFirstTargetObjectEquiv_naturality C w X Y) U V ≅
    (Functor.const SimplexCategoryᵒᵖ).obj
      ((⟨U⟩ : WideSubcategory C.weakEquivalences) ⟶ ⟨V⟩) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    apply ConcreteCategory.hom_ext
    intro f
    change (𝟙 _) ≫ f ≫ (𝟙 _) = f
    simp only [Category.id_comp, Category.comp_id])

def freeFirstHomSpaceMap (U V : C.category) :=
  homSpaceMap (freeFirstMarkedObjectEquiv C) (freeFirstTargetObjectEquiv C w X Y)
    (freeFirstMarkedObjectEquiv_naturality C w X Y)
    (freeFirstTargetObjectEquiv_naturality C w X Y) (freeForwardForwardAugmentation C w X Y)
    (freeFirstMarkedObjectEquiv_augmentation C w X Y) U V

lemma freeFirstSourceHomIso_augmentation (U V : C.category) :
    (freeFirstSourceHomIso C w X Y U V).hom ≫ freeResolutionCanonicalMarkedHomAugmentation C U V =
      freeFirstHomSpaceMap C w X Y U V ≫ (freeFirstTargetHomIso C w X Y U V).hom := by
  ext n f
  apply WideSubcategory.hom_ext
  change (eqToHom _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap ((freeResolutionAugmentationNatTrans C).app n)).map
    (eqToHom _ ≫ f ≫ eqToHom _) ≫ eqToHom _).hom =
      (eqToHom _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap ((freeResolutionAugmentationNatTrans C).app n)).map f ≫
        eqToHom _).hom
  simp only [Functor.map_comp, WideSubcategory.comp_def, marked_eqToHom_hom,
    eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

lemma freeFirstHomSpaceMap_weak (U V : C.category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (freeFirstHomSpaceMap C w X Y U V) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (freeFirstSourceHomIso C w X Y U V)).isWeakHomotopyEquivalence.comp
      (freeResolutionCanonicalMarkedHomAugmentation_weak C U V)
  rw [freeFirstSourceHomIso_augmentation] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (freeFirstTargetHomIso C w X Y U V)).isWeakHomotopyEquivalence.cancel_right h
end SerrePositivity.EInfinity.Hammock.FirstColumn
