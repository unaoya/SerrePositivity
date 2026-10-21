module

public import SerrePositivity.EInfinity.Hammock.WordBackwardDecomposition
public import SerrePositivity.EInfinity.Hammock.WordPaddedBackwardBounds
public import SerrePositivity.EInfinity.Hammock.MiddleBackwardContextErasureComparison

/-!
# 両隣に backward 列を持つ任意の元の列の挿入比較

概要：局所分解の比較を元の語と指定列へ戻し、padding された内部列にも適用する。
方針：語の厳密な等式と指定列の cast を同時に移送する。
規約：元の eraseInclusion の graph 写像自身を結論とする。
使われ方：padding された語の一列挿入と有限個の挿入の比較。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory HomotopicalAlgebra SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{v} C] [ModelCategory C] (X Y : C)

lemma erasureGraphMap_transport {a b : Word} (h : a = b) (j : Fin a.length) :
    IsWeakHomotopyEquivalence
      ((graphDiagram (weakEquivalences C) X Y).map (Word.eraseInclusion a j)) ↔
    IsWeakHomotopyEquivalence ((graphDiagram (weakEquivalences C) X Y).map
      (Word.eraseInclusion b (Fin.cast (congrArg Word.length h) j))) := by
  cases h
  rfl

variable (cof : MorphismProperty.FunctorialFactorizationData
  (cofibrations C) (trivialFibrations C))

include cof in
lemma backwardColumnGraphMap_isWeakHomotopyEquivalence {w : Word} {p : Fin w.length}
    (h : Word.BackwardBounds w p) : IsWeakHomotopyEquivalence
      ((graphDiagram (weakEquivalences C) X Y).map (Word.eraseInclusion w p)) := by
  have hk := MiddleBackward.Context.Erasure.graphMap_isWeakHomotopyEquivalence
    h.prefixWord h.suffixWord h.leftLength h.rightLength X Y cof
  have hj : Fin.cast (congrArg Word.length h.whole_eq)
      (MiddleBackward.Context.middleColumn h.prefixWord h.suffixWord h.leftLength h.rightLength) =
        p := h.middle_column_cast
  have ht := (erasureGraphMap_transport X Y h.whole_eq
    (MiddleBackward.Context.middleColumn h.prefixWord h.suffixWord h.leftLength h.rightLength)).1 hk
  rw [hj] at ht
  exact ht

include cof in
lemma paddedErasedGraphMap_isWeakHomotopyEquivalence (w : Word) (p : Fin w.length)
    (hp : w.direction p = .backward) : IsWeakHomotopyEquivalence
      ((graphDiagram (weakEquivalences C) X Y).map
        (Word.eraseInclusion (Word.paddingFunctor.obj w) (Word.paddedColumn w p))) :=
  backwardColumnGraphMap_isWeakHomotopyEquivalence X Y cof (Word.paddedBackwardBounds w p hp)

end SerrePositivity.EInfinity.Hammock
