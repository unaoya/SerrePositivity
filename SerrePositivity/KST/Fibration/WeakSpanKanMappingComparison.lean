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
variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 元の Verdier 分数の全 strict Kan 図式から、同じ商の coslice 図式への自然変換。 -/
def weakSpanKanMappingComparison :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanDiagram i x ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanMappingDiagram q.hom x :=
  _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanComparison q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts x

/-- 同じ比較は、元の分数図式自身を始点とする全関手 ∞ 圏内の実際の辺。 -/
def weakSpanKanMappingComparisonEdge :
    Edge (functorVertex (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanCoherentDiagram i x))
      (functorVertex (kanDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanMappingDiagram q.hom x))) :=
  _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionSimplexKanComparisonEdge q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts x

end SerrePositivity.KST.Fibration
