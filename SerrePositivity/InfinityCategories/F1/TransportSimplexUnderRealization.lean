module

public import SerrePositivity.InfinityCategories.F1.TransportSimplexUnderComparison
public import SerrePositivity.InfinityCategories.F1.RelativeSectionJointComparison
public import SerrePositivity.InfinityCategories.F1.TransportSimplexSectionDiagram

/-!
概要：単体の共同切断図式を under の共同切断図式と全高次で比較する。
方針：自然な定義域の比較とその成分の同値性を共同実現の一般定理へ適用する。
規約：底の充填性を仮定せず、全対象を同時に保持する。
使われ方：初頂点写像の引き戻しの strict transport と大域的な straightening の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：単体と under の切断図式の実現は全対象上で一つの関手同型。
方針：定義域図式の自然変換の共同実現と成分の同値性を使う。
規約：各対象の比較を独立に選ばない。
使われ方：通常の圏上の strict transport の分類との接続。 -/
def transportSimplexUnderRealizationIso (B : SSet.{u}) :
    FunctorIso (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).realization
      (relativeSectionEnrichedDiagram (transportSimplexUnderDomains B)).realization :=
  relativeSectionRealizationComparisonIso (transportSimplexUnderDomainTransformation B)
    (fun s p ↦ transportSimplexUnderPre_isQCatEquivalence p.val.hom s)

/-- 概要：単体の共同切断図式と under の共同切断図式の全パラメーター上の同型。
方針：同じ比較を二変数交換後の共同図式で回収する。
規約：面と退化、全対象と全高次の相対射を同時に保つ。
使われ方：局所化を用いて一般の底へ比較を降ろす入力。 -/
def transportSimplexUnderJointIso (B : SSet.{u}) :
    FunctorIso (transportSimplexSectionInfinity B)
      (relativeSectionDiagramInfinity (transportSimplexUnderDomains B)) :=
  relativeSectionDiagramInfinityComparisonIso (transportSimplexUnderDomainTransformation B)
    (fun s p ↦ transportSimplexUnderPre_isQCatEquivalence p.val.hom s)

end SerrePositivity.InfinityCategories
