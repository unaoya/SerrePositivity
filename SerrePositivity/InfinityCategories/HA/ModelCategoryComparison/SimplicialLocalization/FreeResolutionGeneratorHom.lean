module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionUnderlyingHom

/-!
# 元の標準生成対象の表示による自由解像の Hom

概要：元の自由解像の同じ Hom を標準生成対象の表示で扱う。
方針：証明済みの元の対象表示の等式から全作用素での自然性を回収する。
規約：元の全作用素を変更せず、追加退化の計算だけに標準表示を使う。
使われ方：元の Hom augmentation の収縮。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.Opposite

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def freeResolutionHomObject (n : SimplexCategoryᵒᵖ) (X : C.category) :
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n).category :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorObject C (n.unop.len + 1) X

lemma freeResolutionObject_eq_homObject (n : SimplexCategoryᵒᵖ) (X : C.category) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C n X = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHomObject C n X :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_generator C n.unop.len X

lemma freeResolutionHomObject_naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (X : C.category) : ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).map θ).functor.obj (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHomObject C n X) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHomObject C m X := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_eq_homObject, ← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_eq_homObject]
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X

def freeResolutionGeneratorHom (X Y : C.category) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.functor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionUnderlyingDiagram C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHomObject C)
    (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHomObject_naturality C θ X) X Y

lemma freeResolutionHomObject_augmentation (n : SimplexCategoryᵒᵖ) (X : C.category) :
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app n).functor.obj
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHomObject C n X) = X :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorObject_augmentation C (n.unop.len + 1) X

def freeResolutionGeneratorHomAugmentation (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorHom C X Y ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (X ⟶ Y) := by
  let η := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientNatTrans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionUnderlyingDiagram C)
    ((Functor.const SimplexCategoryᵒᵖ).obj C.category) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHomObject C)
    (fun _ (X : C.category) => X) (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHomObject_naturality C θ X)
    (fun _ _ => rfl) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionUnderlyingAugmentation C) id
    (fun n X => by exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHomObject_augmentation C n X) X Y
  refine { app := η.app, naturality := ?_ }
  intro n m θ
  apply ConcreteCategory.hom_ext
  intro f
  simpa [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorHom, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.functor, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.map]
    using ConcreteCategory.congr_hom (η.naturality θ) f

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
