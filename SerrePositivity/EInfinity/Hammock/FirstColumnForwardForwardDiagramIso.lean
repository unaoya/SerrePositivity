module

public import SerrePositivity.EInfinity.Hammock.FirstColumnForwardForwardDiagram
public import SerrePositivity.EInfinity.Hammock.FirstColumnForwardForwardCatIso
public import SerrePositivity.EInfinity.Hammock.FirstColumnForwardForwardRelativeFunctor
public import SerrePositivity.EInfinity.Hammock.FixedObjectZigzagDiagram
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramDiagonal

/-!
# 元の前向き二列の圏・graph 図式と対角の自然同型

概要：元の全相対作用素と両端の表示を保って比較を図式に束ねる。
方針：元の切断関手の全自然性と底・両係数の関手則を使う。
規約：元の全圏・graph と同じ augmentation を保持する。
使われ方：DK10.3・5.7の元の対角比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v wO
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite SimplicialLocalization
section Diagram
variable {I : Type v} [Category I] (D : I ⥤ RelativeCategory.{u}) {O : Type wO}
  (p : (i : I) → O → (D.obj i).category)
  (hp : ∀ {i j : I} (θ : i ⟶ j) (X : O), (D.map θ).functor.obj (p i X) = p j X)
  (w : Word) (X Y : O)

def forwardForwardCategoryDiagramIso : FixedObjectDiagram.zigzagDiagram D p hp
    (Word.append (Word.single .forward) (Word.cons .forward w)) X Y ≅
      forwardForwardDiagram D p hp w X Y ⋙ TwoSidedDiagram.totalFunctor :=
  NatIso.ofComponents
    (fun i => forwardForwardCatIso (D.obj i).weakEquivalences w (p i X) (p i Y)) (by
      intro i j θ
      apply Cat.Hom.ext
      exact forwardForward_relative_functor w (D.map θ) (hp θ X) (hp θ Y))

def forwardForwardGraphDiagramIso : FixedObjectDiagram.graphDiagram D p hp
    (Word.append (Word.single .forward) (Word.cons .forward w)) X Y ≅
      forwardForwardDiagram D p hp w X Y ⋙ TwoSidedDiagram.totalFunctor ⋙ nerveFunctor :=
  ((CategoryTheory.Functor.whiskeringRight (C := I) (D := Cat.{u, u})
    (E := SSet.{u})).obj nerveFunctor).mapIso (forwardForwardCategoryDiagramIso D p hp w X Y)

lemma forwardForwardGraphDiagramIso_hom_app (i : I) :
    (forwardForwardGraphDiagramIso D p hp w X Y).hom.app i =
      nerveMap (forwardForwardFunctor (D.obj i).weakEquivalences w (p i X) (p i Y)) := rfl
end Diagram
section Diagonal
variable (D : SimplicialObject RelativeCategory.{u}) {O : Type wO}
  (p : (i : SimplexCategoryᵒᵖ) → O → (D.obj i).category)
  (hp : ∀ {i j : SimplexCategoryᵒᵖ} (θ : i ⟶ j) (X : O),
    (D.map θ).functor.obj (p i X) = p j X) (w : Word) (X Y : O)
def forwardForwardDiagonalIso :
    DoubleSimplicial.diagonalFunctor.obj (FixedObjectDiagram.graphDiagram D p hp
      (Word.append (Word.single .forward) (Word.cons .forward w)) X Y) ≅
    TwoSidedDiagram.diagonalTotalNerve (forwardForwardDiagram D p hp w X Y) :=
  DoubleSimplicial.diagonalFunctor.mapIso (forwardForwardGraphDiagramIso D p hp w X Y)

lemma forwardForwardDiagonalIso_hom_app (n : SimplexCategoryᵒᵖ)
    (σ : (DoubleSimplicial.diagonalFunctor.obj (FixedObjectDiagram.graphDiagram D p hp
      (Word.append (Word.single .forward) (Word.cons .forward w)) X Y)).obj n) :
    (forwardForwardDiagonalIso D p hp w X Y).hom.app n σ =
      σ ⋙ forwardForwardFunctor (D.obj n).weakEquivalences w (p n X) (p n Y) := rfl
end Diagonal
end SerrePositivity.EInfinity.Hammock.FirstColumn
