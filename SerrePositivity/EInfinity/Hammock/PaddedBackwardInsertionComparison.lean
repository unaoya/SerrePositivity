module

public import SerrePositivity.EInfinity.Hammock.BackwardColumnErasureComparison
public import SerrePositivity.EInfinity.Hammock.WordPaddedErasureIso

/-!
# 任意の語の backward 一列挿入を padding した元の比較

概要：元の paddingFunctor.map (eraseInclusion w p) の graph 写像が弱同値になる。
方針：元の列の像の比較同型で始域を照合し、局所分解の弱同値性と合成する。
規約：元の写像自身を結論とし、弱同値の anodyne 局所化での反転は仮定しない。
使われ方：有限個の backward 列の挿入による paddedForwardDiagramMap の全成分。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory HomotopicalAlgebra SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] [ModelCategory C] (X Y : C)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

include cof in
lemma paddedBackwardInsertion_isWeakHomotopyEquivalence (w : Word) (p : Fin w.length)
    (hp : w.direction p = .backward) : IsWeakHomotopyEquivalence
      ((graphDiagram (weakEquivalences C) X Y).map
        (Word.paddingFunctor.map (Word.eraseInclusion w p))) := by
  let G := graphDiagram (weakEquivalences C) X Y
  have hi : IsWeakHomotopyEquivalence (G.map (Word.PaddedErasure.eraseIso w p).hom) :=
    FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _ (by infer_instance)
  have he := paddedErasedGraphMap_isWeakHomotopyEquivalence X Y cof w p hp
  have hc := hi.comp he
  rw [← G.map_comp, Word.PaddedErasure.eraseIso_hom_fac] at hc
  exact hc

end SerrePositivity.EInfinity.Hammock
