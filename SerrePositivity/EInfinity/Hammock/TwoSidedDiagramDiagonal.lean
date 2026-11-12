module

public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramBar
public import SerrePositivity.EInfinity.Hammock.DoubleSimplicialWeak

/-!
# 元の単体的二方向図式の対角 Thomason 比較

概要：底と両係数が全次数で動く図式でも、元の対角比較射そのものは弱同値。
方針：全圏と bar の元の関手の自然変換に同じ対角関手を適用する。
規約：各次数の DK9.5を使い、底の Hom や係数の弱同値性は仮定しない。
使われ方：DK10.6(i)の元の単体的 Grothendieck 全圏との比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedDiagram
open CategoryTheory SerrePositivity.InfinityCategories

variable (D : SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u})

def diagonalBar : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (D ⋙ barFunctor)

def diagonalTotalNerve : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (D ⋙ totalFunctor ⋙ nerveFunctor)

def diagonalThomasonMap : diagonalBar D ⟶ diagonalTotalNerve D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (Functor.whiskerLeft D thomasonMap)

lemma diagonalThomasonMap_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (diagonalThomasonMap D) :=
  DoubleSimplicial.diagonalFunctor_map_weak (Functor.whiskerLeft D thomasonMap)
    (fun n => TwoSidedThomason.map_isWeakHomotopyEquivalence
      (D.obj n).left (D.obj n).right)

end SerrePositivity.EInfinity.Hammock.TwoSidedDiagram
