module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeMarkedCategory
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeResolutionMarkedHomContraction

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
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Opposite

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def freeResolutionMarkedDiagram : SimplicialObject Cat.{u, u} :=
  freeResolution C ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryFunctor

def freeResolutionMarkedObject (n : SimplexCategoryᵒᵖ) (X : C.category) :
    (freeResolutionMarkedDiagram C).obj n := ⟨freeResolutionHomObject C n X⟩

lemma freeResolutionMarkedObject_naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (X : C.category) : ((freeResolutionMarkedDiagram C).map θ).toFunctor.obj
      (freeResolutionMarkedObject C n X) = freeResolutionMarkedObject C m X :=
  congrArg (fun Z => (⟨Z⟩ : WideSubcategory ((freeResolution C).obj m).weakEquivalences))
    (freeResolutionHomObject_naturality C θ X)

def freeResolutionNativeMarkedHom (X Y : C.category) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.functor (freeResolutionMarkedDiagram C) (freeResolutionMarkedObject C)
    (fun θ X => freeResolutionMarkedObject_naturality C θ X) X Y

def freeResolutionMarkedAugmentation : freeResolutionMarkedDiagram C ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (Cat.of (WideSubcategory C.weakEquivalences)) :=
  Functor.whiskerRight (freeResolutionAugmentationNatTrans C) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryFunctor ≫
    (Functor.constComp SimplexCategoryᵒᵖ C _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryFunctor).hom

lemma freeResolutionMarkedObject_augmentation (n : SimplexCategoryᵒᵖ) (X : C.category) :
    ((freeResolutionMarkedAugmentation C).app n).toFunctor.obj
      (freeResolutionMarkedObject C n X) = (⟨X⟩ : WideSubcategory C.weakEquivalences) :=
  congrArg (fun Z => (⟨Z⟩ : WideSubcategory C.weakEquivalences))
    (freeResolutionHomObject_augmentation C n X)

def freeResolutionNativeMarkedHomAugmentation (X Y : C.category) :
    freeResolutionNativeMarkedHom C X Y ⟶ (Functor.const SimplexCategoryᵒᵖ).obj
      ((⟨X⟩ : WideSubcategory C.weakEquivalences) ⟶ ⟨Y⟩) := by
  let η := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientNatTrans (freeResolutionMarkedDiagram C)
    ((Functor.const SimplexCategoryᵒᵖ).obj (Cat.of (WideSubcategory C.weakEquivalences)))
    (freeResolutionMarkedObject C) (fun _ (X : C.category) => ⟨X⟩)
    (fun θ X => freeResolutionMarkedObject_naturality C θ X) (fun _ _ => rfl)
    (freeResolutionMarkedAugmentation C) id (freeResolutionMarkedObject_augmentation C) X Y
  refine { app := η.app, naturality := ?_ }
  intro n m θ
  apply ConcreteCategory.hom_ext
  intro f
  simpa [freeResolutionNativeMarkedHom, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.functor, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.map]
    using ConcreteCategory.congr_hom (η.naturality θ) f

end SerrePositivity.EInfinity.SimplicialLocalization
