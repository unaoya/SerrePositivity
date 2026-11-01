module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FixedObjectHammockAugmentation
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.DoubleSimplicialDiagonal

/-!
# 元の全語の対角と augmentation

概要：元の graph の全作用素を保って対角を取る。
方針：元の自然変換と定数図式への標準同型を使う。
規約：元の比較射を保持する。
使われ方：DK5.7の元の自由解像の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FixedObjectDiagram
open CategoryTheory SimplicialLocalization DoubleSimplicial
variable (D : SimplexCategoryᵒᵖ ⥤ RelativeCategory.{u}) (C : RelativeCategory.{u})
  (p : (i : SimplexCategoryᵒᵖ) → C.category → (D.obj i).category)
  (hp : ∀ {i j : SimplexCategoryᵒᵖ} (θ : i ⟶ j) (X : C.category),
    (D.map θ).functor.obj (p i X) = p j X)
  (A : D ⟶ (Functor.const SimplexCategoryᵒᵖ).obj C)
  (ha : ∀ i X, (A.app i).functor.obj (p i X) = X)

def wordDiagonalDiagram (X Y : C.category) : Word ⥤ SSet.{u} :=
  graphWordDiagram D p hp X Y ⋙ diagonalFunctor

def wordDiagonalTargetIso (X Y : C.category) :
    graphWordTarget (I := SimplexCategoryᵒᵖ) C X Y ⋙ diagonalFunctor ≅
      Hammock.graphDiagram C.weakEquivalences X Y :=
  NatIso.ofComponents (fun w =>
    diagonalFunctor.mapIso (Functor.constComp SimplexCategoryᵒᵖ
      (Cat.of (Zigzag C.weakEquivalences w X Y)) nerveFunctor) ≪≫
        diagonalConstantIso (graph C.weakEquivalences w X Y)) (by
    intro a b f
    ext n σ
    rfl)

def wordDiagonalAugmentation (X Y : C.category) : wordDiagonalDiagram D C p hp X Y ⟶
    Hammock.graphDiagram C.weakEquivalences X Y :=
  Functor.whiskerRight (graphWordAugmentation D C p hp A ha X Y) diagonalFunctor ≫
    (wordDiagonalTargetIso C X Y).hom

lemma wordDiagonalAugmentation_app (w : Word) (X Y : C.category) (n : SimplexCategoryᵒᵖ)
    (σ : ((wordDiagonalDiagram D C p hp X Y).obj w).obj n) :
    ((wordDiagonalAugmentation D C p hp A ha X Y).app w).app n σ =
      σ ⋙ Zigzag.Relative.fixedFunctor (A.app n) (ha n X) (ha n Y) := rfl
end SerrePositivity.EInfinity.Hammock.FixedObjectDiagram
