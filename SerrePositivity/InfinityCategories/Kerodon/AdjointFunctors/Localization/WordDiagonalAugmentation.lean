module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHammockAugmentation
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DoubleSimplicialDiagonal

/-!
# 元の全語の対角と augmentation

概要：元の graph の全作用素を保って対角を取る。
方針：元の自然変換と定数図式への標準同型を使う。
規約：元の比較射を保持する。
使われ方：DK5.7の元の自由解像の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
variable (D : SimplexCategoryᵒᵖ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
  (p : (i : SimplexCategoryᵒᵖ) → C.category → (D.obj i).category)
  (hp : ∀ {i j : SimplexCategoryᵒᵖ} (θ : i ⟶ j) (X : C.category),
    (D.map θ).functor.obj (p i X) = p j X)
  (A : D ⟶ (Functor.const SimplexCategoryᵒᵖ).obj C)
  (ha : ∀ i X, (A.app i).functor.obj (p i X) = X)

def wordDiagonalDiagram (X Y : C.category) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectWordDiagram.graphWordDiagram D p hp X Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor

def wordDiagonalTargetIso (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphWordTarget (I := SimplexCategoryᵒᵖ) C X Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram C.weakEquivalences X Y :=
  NatIso.ofComponents (fun w =>
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.mapIso (Functor.constComp SimplexCategoryᵒᵖ
      (Cat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag C.weakEquivalences w X Y)) nerveFunctor) ≪≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalConstantIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph C.weakEquivalences w X Y)) (by
    intro a b f
    ext n σ
    rfl)

def wordDiagonalAugmentation (X Y : C.category) : wordDiagonalDiagram D C p hp X Y ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram C.weakEquivalences X Y :=
  Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphWordAugmentation D C p hp A ha X Y) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor ≫
    (wordDiagonalTargetIso C X Y).hom

lemma wordDiagonalAugmentation_app (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C.category) (n : SimplexCategoryᵒᵖ)
    (σ : ((wordDiagonalDiagram D C p hp X Y).obj w).obj n) :
    ((wordDiagonalAugmentation D C p hp A ha X Y).app w).app n σ =
      σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (A.app n) (ha n X) (ha n Y) := rfl
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
