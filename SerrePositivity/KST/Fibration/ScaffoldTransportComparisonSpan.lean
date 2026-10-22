module
public import SerrePositivity.KST.Fibration.StrictTransportComparisonSpan

/-! # 元の scaffold の埋め込みと二脚の厳密な制限を保持する復元 span -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- inner 置換の選択に、元の scaffold と両脚の制限を含める。 -/
structure ScaffoldTransportComparisonSpan {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [LeftFibration p] extends StrictTransportComparisonSpan p where
  embedding : simplicialReplacement (leftStrictTransportDiagram p) ⟶ total
  innerAnodyne : innerAnodyneExtensions embedding
  embedding_over : embedding ≫ projection =
    simplicialReplacementProjection (leftStrictTransportDiagram p)
  source_restriction : embedding ≫ source = universalScaffold p
  weighted_restriction : embedding ≫ weighted = tautScaffold (leftStrictTransportDiagram p)

/-- 一般の共通 inner 置換から、元の scaffold の制限も捨てずに受け取る。 -/
theorem nonempty_scaffoldTransportComparisonSpan {I : Type u} [Category.{u} I]
    {E : SSet.{u}} (p : E ⟶ nerve I) [LeftFibration p] :
    Nonempty (ScaffoldTransportComparisonSpan p) := by
  obtain ⟨Z, i, t, a, b, hi, ht, hit, hia, hib, ha, hb, ea, eb⟩ :=
    exists_innerFibration_comparison_span
      (simplicialReplacementProjection (leftStrictTransportDiagram p)) p
      (leftStrictTransportWeightedProjection p)
      (universalScaffold p) (tautScaffold (leftStrictTransportDiagram p))
      (universalScaffold_projection p) (tautScaffold_projection (leftStrictTransportDiagram p))
      (universalScaffold_isPrecompositionEquivalence p)
      (tautScaffold_isPrecompositionEquivalence (leftStrictTransportDiagram p))
  exact ⟨{ toStrictTransportComparisonSpan := ⟨Z, t, a, b, ht, ha, hb, ea, eb⟩
           embedding := i
           innerAnodyne := hi
           embedding_over := hit
           source_restriction := hia
           weighted_restriction := hib }⟩

/-- 元の scaffold の対応も含むデータ全体を一度に選ぶ。 -/
def scaffoldTransportComparisonSpan {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [LeftFibration p] : ScaffoldTransportComparisonSpan p :=
  Classical.choice (nonempty_scaffoldTransportComparisonSpan p)

end SerrePositivity.KST.Fibration
