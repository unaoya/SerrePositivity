module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.StrictTransportComparisonSpan

/-! # 元の scaffold の埋め込みと二脚の厳密な制限を保持する復元 span

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open _root_.SerrePositivity.KST.Fibration

/-- inner 置換の選択に、元の scaffold と両脚の制限を含める。 -/
structure ScaffoldTransportComparisonSpan {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] extends _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.StrictTransportComparisonSpan p where
  embedding : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p) ⟶ total
  innerAnodyne : innerAnodyneExtensions embedding
  embedding_over : embedding ≫ projection =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p)
  source_restriction : embedding ≫ source = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.universalScaffold p
  weighted_restriction : embedding ≫ weighted = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p)

/-- 一般の共通 inner 置換から、元の scaffold の制限も捨てずに受け取る。 -/
theorem nonempty_scaffoldTransportComparisonSpan {I : Type u} [Category.{u} I]
    {E : SSet.{u}} (p : E ⟶ nerve I) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan p) := by
  obtain ⟨Z, i, t, a, b, hi, ht, hit, hia, hib, ha, hb, ea, eb⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.exists_innerFibration_comparison_span
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p)) p
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportWeightedProjection p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.universalScaffold p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.universalScaffold_projection p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_projection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.universalScaffold_isPrecompositionEquivalence p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_isPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p))
  exact ⟨{ toStrictTransportComparisonSpan := ⟨Z, t, a, b, ht, ha, hb, ea, eb⟩
           embedding := i
           innerAnodyne := hi
           embedding_over := hit
           source_restriction := hia
           weighted_restriction := hib }⟩

/-- 元の scaffold の対応も含むデータ全体を一度に選ぶ。 -/
def scaffoldTransportComparisonSpan {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan p :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.nonempty_scaffoldTransportComparisonSpan p)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.nonempty_scaffoldTransportComparisonSpan := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.nonempty_scaffoldTransportComparisonSpan

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.scaffoldTransportComparisonSpan (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.scaffoldTransportComparisonSpan := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.scaffoldTransportComparisonSpan

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.casesOn := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.ctorIdx := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.embedding (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.embedding := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.embedding

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.embedding_over := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.embedding_over

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.innerAnodyne := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.innerAnodyne

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.mk := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.noConfusion := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.noConfusionType := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.rec := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.recOn := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.source_restriction := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.source_restriction

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.toStrictTransportComparisonSpan (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.toStrictTransportComparisonSpan := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.toStrictTransportComparisonSpan

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.weighted_restriction := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.weighted_restriction

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.mk.inj := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.mk.injEq := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan.mk.sizeOf_spec
