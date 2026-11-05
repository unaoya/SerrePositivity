module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan

/-! # 元の scaffold の埋め込みと二脚の厳密な制限を保持する復元 span -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.Transport
open SerrePositivity.KST.Fibration

/-- inner 置換の選択に、元の scaffold と両脚の制限を含める。 -/
structure ScaffoldTransportComparisonSpan {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [LeftFibration p] extends _root_.SerrePositivity.InfinityCategories.F1.Transport.StrictTransportComparisonSpan p where
  embedding : simplicialReplacement (leftStrictTransportDiagram p) ⟶ total
  innerAnodyne : innerAnodyneExtensions _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.embedding
  embedding_over : _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.embedding ≫ projection =
    simplicialReplacementProjection (leftStrictTransportDiagram p)
  source_restriction : _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.embedding ≫ source = universalScaffold p
  weighted_restriction : _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.embedding ≫ weighted = tautScaffold (leftStrictTransportDiagram p)

/-- 一般の共通 inner 置換から、元の scaffold の制限も捨てずに受け取る。 -/
theorem nonempty_scaffoldTransportComparisonSpan {I : Type u} [Category.{u} I]
    {E : SSet.{u}} (p : E ⟶ nerve I) [LeftFibration p] :
    Nonempty (_root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan p) := by
  obtain ⟨Z, i, t, a, b, hi, ht, hit, hia, hib, ha, hb, ea, eb⟩ :=
    exists_innerFibration_comparison_span
      (simplicialReplacementProjection (leftStrictTransportDiagram p)) p
      (leftStrictTransportWeightedProjection p)
      (universalScaffold p) (tautScaffold (leftStrictTransportDiagram p))
      (universalScaffold_projection p) (tautScaffold_projection (leftStrictTransportDiagram p))
      (universalScaffold_isPrecompositionEquivalence p)
      (tautScaffold_isPrecompositionEquivalence (leftStrictTransportDiagram p))
  exact ⟨{ _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.toStrictTransportComparisonSpan := ⟨Z, t, a, b, ht, ha, hb, ea, eb⟩
           _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.embedding := i
           _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.innerAnodyne := hi
           _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.embedding_over := hit
           _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.source_restriction := hia
           _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.weighted_restriction := hib }⟩

/-- 元の scaffold の対応も含むデータ全体を一度に選ぶ。 -/
def scaffoldTransportComparisonSpan {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [LeftFibration p] : _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan p :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.F1.Transport.nonempty_scaffoldTransportComparisonSpan p)

end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.nonempty_scaffoldTransportComparisonSpan := _root_.SerrePositivity.InfinityCategories.F1.Transport.nonempty_scaffoldTransportComparisonSpan

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.scaffoldTransportComparisonSpan (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.scaffoldTransportComparisonSpan := _root_.SerrePositivity.InfinityCategories.F1.Transport.scaffoldTransportComparisonSpan

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.casesOn := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.ctorIdx := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.embedding (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.embedding := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.embedding

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.embedding_over := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.embedding_over

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.innerAnodyne := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.innerAnodyne

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.mk := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.noConfusion := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.noConfusionType := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.rec := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.recOn := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.source_restriction := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.source_restriction

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.toStrictTransportComparisonSpan (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.toStrictTransportComparisonSpan := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.toStrictTransportComparisonSpan

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.weighted_restriction := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.weighted_restriction

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.mk.inj := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.mk.injEq := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan.mk.sizeOf_spec
