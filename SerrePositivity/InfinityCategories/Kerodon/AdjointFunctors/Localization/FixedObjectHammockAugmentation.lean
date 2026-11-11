module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectCategoryAugmentation
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitGraph

/-!
# 元の相対 augmentation による固定対象の hammock 図式の比較

概要：全語の固定対象の図式から、元の hammock 余極限への自然な augmentation を得る。
方針：元の圏値の比較を nerve・二方向の交換・余極限へ移す。
規約：定数図式への比較も元の全作用素で検証する。
使われ方：自由相対解像の対角 hammock から元の hammock への左比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u uI vI
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I] (D : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
  (p : (i : I) → C.category → (D.obj i).category)
  (hp : ∀ {i j : I} (θ : i ⟶ j) (X : C.category), (D.map θ).functor.obj (p i X) = p j X)
  (A : D ⟶ (Functor.const I).obj C)
  (ha : ∀ i X, (A.app i).functor.obj (p i X) = X)

def graphWordTarget (X Y : C.category) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ I ⥤ SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.categoryDiagram C.weakEquivalences X Y ⋙ Functor.const I) ⋙
    (CategoryTheory.Functor.whiskeringRight
      (C := I) (D := Cat.{u, u}) (E := SSet.{u})).obj nerveFunctor

lemma graphWordTarget_flip (X Y : C.category) : (graphWordTarget (I := I) C X Y).flip =
    (Functor.const I).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram C.weakEquivalences X Y) := by
  apply CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j θ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

def graphWordAugmentation (X Y : C.category) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram.graphWordDiagram D p hp X Y ⟶
    graphWordTarget (I := I) C X Y :=
  Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.categoryWordAugmentation D C p hp A ha X Y)
    ((CategoryTheory.Functor.whiskeringRight
      (C := I) (D := Cat.{u, u}) (E := SSet.{u})).obj nerveFunctor)

def graphAugmentation (X Y : C.category) : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram.graphWordDiagram D p hp X Y).flip ⟶
    (Functor.const I).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram C.weakEquivalences X Y) :=
  (flipFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word I SSet.{u}).map (graphWordAugmentation D C p hp A ha X Y) ≫
    eqToHom (graphWordTarget_flip (I := I) C X Y)

def hammockAugmentation (X Y : C.category) : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram.graphWordDiagram D p hp X Y).flip ⋙ colim ⟶
    (Functor.const I).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y) :=
  Functor.whiskerRight (graphAugmentation D C p hp A ha X Y) colim ≫
    (Functor.constComp I (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram C.weakEquivalences X Y) colim).hom

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
