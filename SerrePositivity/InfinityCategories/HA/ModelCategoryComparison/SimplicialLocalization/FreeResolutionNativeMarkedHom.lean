module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeMarkedCategory
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionMarkedHomContraction

/-!
# 元の指定部分圏の固定 Hom と augmentation

概要：元の指定部分圏の単体的図式を作り、固定 Hom と元の指定 Hom への射を構成する。
方針：元の標準生成対象の表示と対象保存の等式を wide 部分圏へ送る。
規約：部分圏の Hom は Mathlib の元の Hom 構造体であり、代替の射集合ではない。
使われ方：DK2.4の指定部分圏についての実際の Hom 弱比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.Opposite

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def freeResolutionMarkedDiagram : SimplicialObject Cat.{u, u} :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryFunctor

def freeResolutionMarkedObject (n : SimplexCategoryᵒᵖ) (X : C.category) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMarkedDiagram C).obj n := ⟨_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHomObject C n X⟩

lemma freeResolutionMarkedObject_naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (X : C.category) : ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMarkedDiagram C).map θ).toFunctor.obj
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMarkedObject C n X) = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMarkedObject C m X :=
  congrArg (fun Z => (⟨Z⟩ : WideSubcategory ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj m).weakEquivalences))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHomObject_naturality C θ X)

def freeResolutionNativeMarkedHom (X Y : C.category) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.functor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMarkedDiagram C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMarkedObject C)
    (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMarkedObject_naturality C θ X) X Y

def freeResolutionMarkedAugmentation : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMarkedDiagram C ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (Cat.of (WideSubcategory C.weakEquivalences)) :=
  Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryFunctor ≫
    (Functor.constComp SimplexCategoryᵒᵖ C _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryFunctor).hom

lemma freeResolutionMarkedObject_augmentation (n : SimplexCategoryᵒᵖ) (X : C.category) :
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMarkedAugmentation C).app n).toFunctor.obj
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMarkedObject C n X) = (⟨X⟩ : WideSubcategory C.weakEquivalences) :=
  congrArg (fun Z => (⟨Z⟩ : WideSubcategory C.weakEquivalences))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHomObject_augmentation C n X)

def freeResolutionNativeMarkedHomAugmentation (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionNativeMarkedHom C X Y ⟶ (Functor.const SimplexCategoryᵒᵖ).obj
      ((⟨X⟩ : WideSubcategory C.weakEquivalences) ⟶ ⟨Y⟩) := by
  let η := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientNatTrans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMarkedDiagram C)
    ((Functor.const SimplexCategoryᵒᵖ).obj (Cat.of (WideSubcategory C.weakEquivalences)))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMarkedObject C) (fun _ (X : C.category) => ⟨X⟩)
    (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMarkedObject_naturality C θ X) (fun _ _ => rfl)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMarkedAugmentation C) id (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMarkedObject_augmentation C) X Y
  refine { app := η.app, naturality := ?_ }
  intro n m θ
  apply ConcreteCategory.hom_ext
  intro f
  simpa [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionNativeMarkedHom, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.functor, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.map]
    using ConcreteCategory.congr_hom (η.naturality θ) f

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
