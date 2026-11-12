module

public import SerrePositivity.EInfinity.SimplicialLocalization.KanHammockWeakArrows
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Localization

/-!
# 元の W の辺を反転する実 hammock nerve 関手

概要：元の通常圏の指定射が表す辺の集合と、その反転証明を供給する。
方針：元の射からの coherent な辺との一致と既存の往復ホモトピーを使う。
規約：指定辺集合は元の W だけから定義し、局所化の普遍性とは分ける。
使われ方：全反転関手 ∞ 圏への実際の前合成写像。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory SerrePositivity.InfinityCategories
open scoped Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def weakNerveEdges : Set ((nerve C.category) _⦋1⦌) :=
  {s | ∃ (X Y : C.category) (f : X ⟶ Y),
    C.weakEquivalences f ∧ s = ComposableArrows.mk₁ f}

lemma hammockLocalizationNerveMap_inverts :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (hammockLocalizationNerveMap C) (weakNerveEdges C) := by
  intro s hs
  obtain ⟨X, Y, f, hf, rfl⟩ := hs
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ComposableArrows.mk₁ f)).map
    ((SSet.truncation 2).map (hammockLocalizationNerveMap C)))
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((kanHammockSourceFunctor C).map f)).toTruncated) ?_).2
  · exact kanHammockSourceFunctor_weak_invertible C f hf
  · exact hammockLocalizationNerveMap_arrow C f

end SerrePositivity.EInfinity.SimplicialLocalization
