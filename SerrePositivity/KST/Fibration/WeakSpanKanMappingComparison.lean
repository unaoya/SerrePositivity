module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FractionSimplexKanComparison
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanKanQuotientDescent

/-! # 同じ Verdier 分数図式と商の coslice 写像空間図式の coherent な比較 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 元の Verdier 分数の全 strict Kan 図式から、同じ商の coslice 図式への自然変換。 -/
def weakSpanKanMappingComparison :
    weakSpanKanDiagram i x ⟶ fractionSimplexKanMappingDiagram q.hom x :=
  fractionSimplexKanComparison q.hom (weakEquivalences i) h.inverts x

/-- 同じ比較は、元の分数図式自身を始点とする全関手 ∞ 圏内の実際の辺。 -/
def weakSpanKanMappingComparisonEdge :
    Edge (functorVertex (weakSpanKanCoherentDiagram i x))
      (functorVertex (kanDiagramCoherentNerve (fractionSimplexKanMappingDiagram q.hom x))) :=
  fractionSimplexKanComparisonEdge q.hom (weakEquivalences i) h.inverts x

end SerrePositivity.KST.Fibration
