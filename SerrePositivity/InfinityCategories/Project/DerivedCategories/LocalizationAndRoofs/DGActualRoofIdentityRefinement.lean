module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGActualRoofSpans
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofPointSliceTriangleEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierOverTerminal
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.FullSubcomplexEdgeLift

/-! # 指定実分母から恒等分母への実細分辺

概要：任意の実屋根の分母から恒等分母へ、始域成分を指定分母に保つ実辺を構成する。
方針：指定分母と恒等辺の退化合成三角形を実 slice 辺へ戻し、全部分複体に持ち上げる。
規約：終対象性だけによる辺の選択を使わない。使われ方：屋根の評価三角形の全空間への実装。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 指定実分母から恒等分母への、元の実分母を始域成分に持つ実細分辺。 -/
def dgActualRoofDenominatorIdentityEdge (P : Set D) (x y : D)
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGActualRoofSpan A D P x y) :
    Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofSpanDenominatorVertex A D P x y r) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex A D P x) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullSubcomplexEdgeLift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGVerdierOverVertex A D P x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgActualRoofSpanDenominatorVertex A D P x y r) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverIdentityVertex A D P x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceCompositionEdge (Truncated.Edge.CompStruct.compId r.denominator)).edge
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceCompositionEdge (Truncated.Edge.CompStruct.compId r.denominator)).src_eq
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceCompositionEdge (Truncated.Edge.CompStruct.compId r.denominator)).tgt_eq.trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex_id (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))

/-- 指定実細分辺の台は、元の退化合成三角形による実 slice 辺そのもの。 -/
lemma dgActualRoofDenominatorIdentityEdge_simplex (P : Set D) (x y : D)
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGActualRoofSpan A D P x y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x).ι.app (Opposite.op ⦋1⦌)
      (dgActualRoofDenominatorIdentityEdge A D P x y r).edge =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceCompositionEdge (Truncated.Edge.CompStruct.compId r.denominator)).edge :=
  rfl

/-- 指定実細分辺の始域射影は、元の指定実分母の一次単体。 -/
lemma dgActualRoofDenominatorIdentityEdge_source (P : Set D) (x y : D)
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGActualRoofSpan A D P x y) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋1⦌)
      (dgActualRoofDenominatorIdentityEdge A D P x y r).edge = r.denominator.edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))).app
      (Opposite.op ⦋1⦌) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x).ι.app (Opposite.op ⦋1⦌)
        (dgActualRoofDenominatorIdentityEdge A D P x y r).edge) = _
  rw [dgActualRoofDenominatorIdentityEdge_simplex]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceCompositionEdge_projection _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
