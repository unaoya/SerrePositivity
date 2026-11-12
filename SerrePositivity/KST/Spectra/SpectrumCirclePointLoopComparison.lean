module

public import SerrePositivity.KST.Spectra.SpectrumPointLoopReference
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace

/-!
概要：円評価錐から、同じ固定図式上の BF homotopy limit 錐への実際の比較。
方針：参照極限錐の終対象性で slice 内の辺を取り、底と両端を保持する拡張を取り出す。
規約：比較頂点の可逆性はまだ主張しない。使われ方：元の普遍評価との比較射の照合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circlePointLoopComparisonSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 固定 cospan 上の円評価錐から、元の BF 極限錐への slice 内の実際の辺。 -/
def circlePointLoopConeComparison (z : Sp.{u} _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (pointLoopCospan (nativeCotensorInput PointedSimplicialSet.circle z).val)).Edge
      (nativeCirclePointLoopCone z)
      (pointLoopReferenceCone (nativeCotensorInput PointedSimplicialSet.circle z).val) := by
  let e := Classical.choice
    ((pointLoopReferenceCone_isLimit
      (nativeCotensorInput PointedSimplicialSet.circle z).val).nonempty_edge
        (nativeCirclePointLoopCone z))
  exact SSet.Edge.mk e.edge e.src_eq e.tgt_eq

/-- 比較錐の射を頂点へ射影して得る、元の Sp 内の実際の比較辺。 -/
def circlePointLoopComparisonEdge (z : Sp.{u} _⦋0⦌) :
    Sp.{u}.Edge (nativeCirclePointLoopCone z).vertex
      (pointLoopReferenceCone (nativeCotensorInput PointedSimplicialSet.circle z).val).vertex :=
  (circlePointLoopConeComparison z).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (pointLoopCospan (nativeCotensorInput PointedSimplicialSet.circle z).val))

/-- 同じ比較辺を、元の BF cotensor と BF homotopy limit の厳密な端点で表示。 -/
def circlePointLoopComparisonBFEdge (z : Sp.{u} _⦋0⦌) :
    Sp.{u}.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex
      (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex
        (homotopyLimit
          (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val))) :=
  (circlePointLoopComparisonEdge z).ofEq (nativeCirclePointLoopCone_vertex z)
    (pointLoopReferenceCone_vertex _)

/-- 実際の錐の射が定める、元の BF cotensor から BF homotopy limit への通常の射。 -/
def circlePointLoopComparison (z : Sp.{u} _⦋0⦌) :
    cotensor PointedSimplicialSet.circle (nativeCotensorInput PointedSimplicialSet.circle z).val ⟶
      homotopyLimit (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom (circlePointLoopComparisonBFEdge z)

/-- 通常の比較射の coherent な辺は、元の錐の射から取り出した辺そのもの。 -/
lemma circlePointLoopComparison_edge (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (circlePointLoopComparison z) = circlePointLoopComparisonBFEdge z :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_hom _

/-- 比較は底の cospan 全体を固定した、二つの錐を結ぶ実際の join 図式。 -/
def circlePointLoopComparisonExtension (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[1] : SSet.{u + 1}) (horn 2 2 : SSet.{u + 1}) ⟶ Sp.{u} :=
  (circlePointLoopConeComparison z).edge.val

/-- 比較の拡張は、元の固定 cospan 全体を厳密に保持する。 -/
lemma circlePointLoopComparisonExtension_base (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[1] : SSet.{u + 1}) (horn 2 2) ≫ circlePointLoopComparisonExtension z =
      pointLoopCospan (nativeCotensorInput PointedSimplicialSet.circle z).val :=
  (circlePointLoopConeComparison z).edge.property

/-- 比較の拡張の始点は、元の円評価錐全体そのもの。 -/
lemma circlePointLoopComparisonExtension_source (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 (horn 2 2 : SSet.{u + 1})) ≫
        circlePointLoopComparisonExtension z = (nativeCirclePointLoopCone z).val :=
  congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver
    (pointLoopCospan (nativeCotensorInput PointedSimplicialSet.circle z).val)) _⦋0⦌ ↦ t.val)
      (circlePointLoopConeComparison z).src_eq

/-- 比較の拡張の終点は、元の BF homotopy limit の参照錐全体そのもの。 -/
lemma circlePointLoopComparisonExtension_target (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 (horn 2 2 : SSet.{u + 1})) ≫
        circlePointLoopComparisonExtension z =
      (pointLoopReferenceCone (nativeCotensorInput PointedSimplicialSet.circle z).val).val :=
  congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver
    (pointLoopCospan (nativeCotensorInput PointedSimplicialSet.circle z).val)) _⦋0⦌ ↦ t.val)
      (circlePointLoopConeComparison z).tgt_eq

/-- 比較の拡張の頂点方向は、錐の比較辺を厳密に回収する。 -/
lemma circlePointLoopComparisonExtension_apex (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[1] : SSet.{u + 1}) (horn 2 2) ≫ circlePointLoopComparisonExtension z =
      SSet.yonedaEquiv.symm (circlePointLoopComparisonEdge z).edge := by
  change _ = SSet.yonedaEquiv.symm (SSet.yonedaEquiv _)
  rw [Equiv.symm_apply_apply]
  rfl

/-- 固定図式上の別の比較錐の射を使っても、頂点の比較射のホモトピー類は同じ。 -/
lemma circlePointLoopComparisonEdge_ho_unique (z : Sp.{u} _⦋0⦌)
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver
      (pointLoopCospan (nativeCotensorInput PointedSimplicialSet.circle z).val)).Edge
        (nativeCirclePointLoopCone z)
        (pointLoopReferenceCone (nativeCotensorInput PointedSimplicialSet.circle z).val)) :
    SSet.Truncated.HomotopyCategory.homMk
        (e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
          (pointLoopCospan (nativeCotensorInput PointedSimplicialSet.circle z).val))).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (circlePointLoopComparisonEdge z).toTruncated := by
  have h := (pointLoopReferenceCone_isLimit
    (nativeCotensorInput PointedSimplicialSet.circle z).val).isTerminalHo.hom_ext
      (SSet.Truncated.HomotopyCategory.homMk e.toTruncated)
      (SSet.Truncated.HomotopyCategory.homMk (circlePointLoopConeComparison z).toTruncated)
  have hp := congrArg ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
    (pointLoopCospan (nativeCotensorInput PointedSimplicialSet.circle z).val))).toFunctor.map) h
  exact hp

end SerrePositivity.KST.Spectra.OmegaSpectrum
