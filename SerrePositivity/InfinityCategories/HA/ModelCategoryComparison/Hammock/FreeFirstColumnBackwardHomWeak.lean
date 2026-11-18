module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeFirstColumnBackwardObjects
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeFirstColumnHomWeak

/-!
# 後向き二列の元の底の Hom 比較の弱同値性

概要：元の自由解像の同じ底の指定 Hom augmentation の弱同値性を回収する。
方針：係数から独立な底の比較を既存の native 指定 Hom の正方形へ戻す。
規約：底の弱同値性を新たな仮定にしない。
使われ方：DK10.4–10.6の後向き二列への適用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C.category)
def freeBackwardFirstTargetObjectEquiv (n : SimplexCategoryᵒᵖ) : C.category ≃
    (((Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardData C w X Y)).obj n).base :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.markedObjectEquiv C
lemma freeBackwardFirstTargetObjectEquiv_naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (Z : C.category) :
    ((((Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardData C w X Y)).map θ).base.obj
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeBackwardFirstTargetObjectEquiv C w X Y n Z)) = 
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeBackwardFirstTargetObjectEquiv C w X Y m Z := rfl

def freeBackwardFirstSourceHomIso (U V : C.category) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.homSpace (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeBackwardBackwardDiagram C w X Y) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstMarkedObjectEquiv C)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeBackwardFirstMarkedObjectEquiv_naturality C w X Y) U V ≅
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionCanonicalMarkedHom C U V :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

def freeBackwardFirstTargetHomIso (U V : C.category) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.homSpace ((Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardData C w X Y))
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeBackwardFirstTargetObjectEquiv C w X Y) 
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeBackwardFirstTargetObjectEquiv_naturality C w X Y) U V ≅
    (Functor.const SimplexCategoryᵒᵖ).obj
      ((⟨U⟩ : WideSubcategory C.weakEquivalences) ⟶ ⟨V⟩) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    apply ConcreteCategory.hom_ext
    intro f
    change (𝟙 _) ≫ f ≫ (𝟙 _) = f
    simp only [Category.id_comp, Category.comp_id])

def freeBackwardFirstHomSpaceMap (U V : C.category) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.FixedVertices.homSpaceMap (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstMarkedObjectEquiv C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeBackwardFirstTargetObjectEquiv C w X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeBackwardFirstMarkedObjectEquiv_naturality C w X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeBackwardFirstTargetObjectEquiv_naturality C w X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeBackwardBackwardAugmentation C w X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeBackwardFirstMarkedObjectEquiv_augmentation C w X Y) U V

lemma freeBackwardFirstSourceHomIso_augmentation (U V : C.category) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeBackwardFirstSourceHomIso C w X Y U V).hom ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionCanonicalMarkedHomAugmentation C U V =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeBackwardFirstHomSpaceMap C w X Y U V ≫
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeBackwardFirstTargetHomIso C w X Y U V).hom := by
  ext n f
  apply WideSubcategory.hom_ext
  change (eqToHom _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app n)).map
    (eqToHom _ ≫ f ≫ eqToHom _) ≫ eqToHom _).hom =
      (eqToHom _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app n)).map f ≫
        eqToHom _).hom
  simp only [Functor.map_comp, WideSubcategory.comp_def, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.marked_eqToHom_hom,
    eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

lemma freeBackwardFirstHomSpaceMap_weak (U V : C.category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeBackwardFirstHomSpaceMap C w X Y U V) := by
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstHomSpaceMap_weak C w X Y U V
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
