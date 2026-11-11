module

public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramDiagonal

/-!
# 元の単体的二方向比較射の対角での自然性

概要：底と両係数の元の自然変換による対角の比較を同じ射で照合する。
方針：元の各次数の Thomason 正方形を同じ対角へ移す。
規約：元の全圏と bar の対角射の弱同値性は同値であり、入力へ移さない。
使われ方：DK10.4–10.6の係数・底の弱不変性の回収。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedDiagram
open CategoryTheory SerrePositivity.InfinityCategories

variable {D E : SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u}} (τ : D ⟶ E)

def diagonalBarMap : diagonalBar D ⟶ diagonalBar E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (Functor.whiskerRight τ barFunctor)

def diagonalTotalMap : diagonalTotalNerve D ⟶ diagonalTotalNerve E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map
    (Functor.whiskerRight τ (totalFunctor ⋙ nerveFunctor))

lemma diagonalThomasonMap_naturality :
    diagonalThomasonMap D ≫ diagonalTotalMap τ =
      diagonalBarMap τ ≫ diagonalThomasonMap E := by
  ext n e
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (thomasonMap.naturality (τ.app n)).symm n) e

lemma diagonalMap_weak_iff :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (diagonalTotalMap τ) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (diagonalBarMap τ) := by
  constructor
  · intro h
    have hc := (diagonalThomasonMap_isWeakHomotopyEquivalence D).comp h
    rw [diagonalThomasonMap_naturality τ] at hc
    exact (diagonalThomasonMap_isWeakHomotopyEquivalence E).cancel_right hc
  · intro h
    have hc := h.comp (diagonalThomasonMap_isWeakHomotopyEquivalence E)
    rw [← diagonalThomasonMap_naturality τ] at hc
    exact (diagonalThomasonMap_isWeakHomotopyEquivalence D).cancel_left hc

end SerrePositivity.EInfinity.Hammock.TwoSidedDiagram
