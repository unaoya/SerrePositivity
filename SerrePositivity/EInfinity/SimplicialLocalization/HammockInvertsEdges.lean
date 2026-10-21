module

public import SerrePositivity.EInfinity.SimplicialLocalization.KanHammockWeakArrows
public import SerrePositivity.InfinityCategories.F1B.Localization

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
variable (C : RelativeCategory.{u})

def weakNerveEdges : Set ((nerve C.category) _⦋1⦌) :=
  {s | ∃ (X Y : C.category) (f : X ⟶ Y),
    C.weakEquivalences f ∧ s = ComposableArrows.mk₁ f}

lemma hammockLocalizationNerveMap_inverts :
    InvertsEdges (hammockLocalizationNerveMap C) (weakNerveEdges C) := by
  intro s hs
  obtain ⟨X, Y, f, hf, rfl⟩ := hs
  apply (isInvertibleEdge_congr (e := (edgeOfSimplex (ComposableArrows.mk₁ f)).map
    ((SSet.truncation 2).map (hammockLocalizationNerveMap C)))
    (f := (coherentNerveEdge ((kanHammockSourceFunctor C).map f)).toTruncated) ?_).2
  · exact kanHammockSourceFunctor_weak_invertible C f hf
  · exact hammockLocalizationNerveMap_arrow C f

end SerrePositivity.EInfinity.SimplicialLocalization
