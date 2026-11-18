module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumnForwardForwardDiagonalAugmentation
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockObjects
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionCanonicalMarkedHom

/-!
# 元の自由解像の前向き二列の係数と指定対象の表示

概要：元の各自由次数の二方向図式と augmentation、指定部分圏の対象表示の全単射を得る。
方針：元の対象の augmentation と全作用素の等式を使う。
規約：元の指定部分圏の対象・全射を保つ。
使われ方：DK10.4–10.6の元の固定頂点の入力への代入。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
def markedObjectEquiv : C.category ≃ WideSubcategory C.weakEquivalences where
  toFun X := ⟨X⟩
  invFun X := X.obj
  left_inv _ := rfl
  right_inv _ := rfl

def freeForwardForwardDiagram (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C.category) :
    SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardDiagram (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C)
    (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X) w X Y

def freeForwardForwardAugmentation (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeForwardForwardDiagram C w X Y ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardData C w X Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardAugmentation (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C) C (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C)
    (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C) w X Y

def freeFirstMarkedObjectEquiv (n : SimplexCategoryᵒᵖ) :
    C.category ≃ WideSubcategory ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n).weakEquivalences :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObjectEquiv C n).symm.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.markedObjectEquiv ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n))

lemma freeFirstMarkedObjectEquiv_apply (n : SimplexCategoryᵒᵖ) (X : C.category) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstMarkedObjectEquiv C n X =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.markedObject (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C) n X := rfl
lemma freeFirstMarkedObjectEquiv_naturality (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C.category)
    {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (Z : C.category) :
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeForwardForwardDiagram C w X Y).map θ).base.obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstMarkedObjectEquiv C n Z) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstMarkedObjectEquiv C m Z :=
  congrArg (fun Z => (⟨Z⟩ : WideSubcategory ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj m).weakEquivalences))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ Z)
lemma freeFirstMarkedObjectEquiv_augmentation (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C.category)
    (n : SimplexCategoryᵒᵖ) (Z : C.category) :
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeForwardForwardAugmentation C w X Y).app n).base.obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.freeFirstMarkedObjectEquiv C n Z) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.markedObjectEquiv C Z :=
  congrArg (fun Z => (⟨Z⟩ : WideSubcategory C.weakEquivalences))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n Z)
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
