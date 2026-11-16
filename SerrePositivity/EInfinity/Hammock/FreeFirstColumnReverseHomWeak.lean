module

public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnReverseObjects
public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnHomWeak

/-!
# 混合二方向の元の底の Hom 比較の弱同値性

概要：元の自由解像の同じ底の指定 Hom augmentation の弱同値性を回収する。
方針：係数から独立な底の比較を既存の native 指定 Hom の正方形へ戻す。
規約：底の弱同値性を新たな仮定にしない。
使われ方：DK10.4–10.6の混合二方向への適用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization SerrePositivity.InfinityCategories
open TwoSidedDiagram.FixedVertices
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C.category)
def freeReverseFirstTargetObjectEquiv (n : SimplexCategoryᵒᵖ) : C.category ≃
    (((Functor.const SimplexCategoryᵒᵖ).obj (backwardForwardData C w X Y)).obj n).base :=
  markedObjectEquiv C
lemma freeReverseFirstTargetObjectEquiv_naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (Z : C.category) :
    ((((Functor.const SimplexCategoryᵒᵖ).obj (backwardForwardData C w X Y)).map θ).base.obj
      (freeReverseFirstTargetObjectEquiv C w X Y n Z)) = 
        freeReverseFirstTargetObjectEquiv C w X Y m Z := rfl

def freeReverseFirstSourceHomIso (U V : C.category) :
    homSpace (freeBackwardForwardDiagram C w X Y) (freeFirstMarkedObjectEquiv C)
      (freeReverseFirstMarkedObjectEquiv_naturality C w X Y) U V ≅
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionCanonicalMarkedHom C U V :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

def freeReverseFirstTargetHomIso (U V : C.category) :
    homSpace ((Functor.const SimplexCategoryᵒᵖ).obj (backwardForwardData C w X Y))
      (freeReverseFirstTargetObjectEquiv C w X Y) 
      (freeReverseFirstTargetObjectEquiv_naturality C w X Y) U V ≅
    (Functor.const SimplexCategoryᵒᵖ).obj
      ((⟨U⟩ : WideSubcategory C.weakEquivalences) ⟶ ⟨V⟩) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    apply ConcreteCategory.hom_ext
    intro f
    change (𝟙 _) ≫ f ≫ (𝟙 _) = f
    simp only [Category.id_comp, Category.comp_id])

def freeReverseFirstHomSpaceMap (U V : C.category) :=
  homSpaceMap (freeFirstMarkedObjectEquiv C) (freeReverseFirstTargetObjectEquiv C w X Y)
    (freeReverseFirstMarkedObjectEquiv_naturality C w X Y)
    (freeReverseFirstTargetObjectEquiv_naturality C w X Y)
    (freeBackwardForwardAugmentation C w X Y)
    (freeReverseFirstMarkedObjectEquiv_augmentation C w X Y) U V

lemma freeReverseFirstSourceHomIso_augmentation (U V : C.category) :
    (freeReverseFirstSourceHomIso C w X Y U V).hom ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionCanonicalMarkedHomAugmentation C U V =
      freeReverseFirstHomSpaceMap C w X Y U V ≫
        (freeReverseFirstTargetHomIso C w X Y U V).hom := by
  ext n f
  apply WideSubcategory.hom_ext
  change (eqToHom _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app n)).map
    (eqToHom _ ≫ f ≫ eqToHom _) ≫ eqToHom _).hom =
      (eqToHom _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app n)).map f ≫
        eqToHom _).hom
  simp only [Functor.map_comp, WideSubcategory.comp_def, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.marked_eqToHom_hom,
    eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

lemma freeReverseFirstHomSpaceMap_weak (U V : C.category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (freeReverseFirstHomSpaceMap C w X Y U V) := by
  exact freeFirstHomSpaceMap_weak C w X Y U V
end SerrePositivity.EInfinity.Hammock.FirstColumn
