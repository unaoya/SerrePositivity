module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.PointHomTransportEdge
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.Reindexing.ConstantPrecompositionFactor
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.NativeCoconeFamilyEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.RealizedCoconeComparison

/-!
概要：元の余錐の全 Hom の作用は、native 単位と同じ頂点辺の定値変換の合成を表す。
方針：元の輸送円柱の指定点の辺に、同じ coslice の余錐変換の可換式を適用する。
規約：指定余錐・頂点辺・全作用先の余錐を保持し、余極限性は要求しない。
使われ方：実際の前層余極限脚の標準単位正方形を全余錐作用へ移す。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SSet.Truncated.HomotopyCategory
variable {K X : SSet.{u}} [Quasicategory X] {F : K ⟶ X}
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) {y : X _⦋0⦌} (e : SSet.Edge c.vertex y)

/-- 指定した同じ頂点辺による全 Hom の作用先を、元の図式上の余錐として保持する。 -/
def coconeEdgeAction : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily c y).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftHomEdgePoint e)).val

/-- 元の全 Hom の作用先の頂点は、元の指定辺の終点そのもの。 -/
lemma coconeEdgeAction_vertex : (coconeEdgeAction c e).vertex = y :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily c y).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftHomEdgePoint e)).property.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero y)

/-- 同じ元の輸送円柱の指定辺を、元の余錐から同じ作用先への辺として保持する。 -/
def coconeEdgeActionTransport :
    SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F)) c (coconeEdgeAction c e) :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomTransportCylinderEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F) c y (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftHomEdgePoint e)).toTruncated

/-- 元の作用先へ向かう全余錐の頂点変換は、指定した同じ辺の定値関手像。 -/
lemma coconeEdgeActionTransport_top :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeTop c (coconeEdgeAction c e)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorEdge (coconeEdgeActionTransport c e)).toTruncated).edge =
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantFunctorEdge (A := K) e.toTruncated).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeWholeEdgeTop_constant]
  have ha := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorEdge_apex (coconeEdgeActionTransport c e)
  exact congrArg (fun a => (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K X).app (Opposite.op ⦋1⦌) a)
    (ha.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomTransportCylinderEdge_projection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F) c y e))

omit [Quasicategory X] in
/-- 頂点を等式で指定して読んだ余錐変換は、元の全一単体を変更しない。 -/
lemma coconeTransformationPointAt_edge (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) {z : X _⦋0⦌}
    (hz : d.vertex = z) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeTransformationPointAt d hz)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex d)).edge := by
  subst z
  rfl

/-- 元の全作用先の余錐変換は、元の native 単位と同じ頂点辺の定値変換の合成類。 -/
lemma coconeEdgeAction_unit_square :
    homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeTransformationPointAt
      (coconeEdgeAction c e) (coconeEdgeAction_vertex c e))).toTruncated =
    homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex c)).toTruncated ≫
      homMk (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantFunctorEdge (A := K) e.toTruncated) := by
  let d := coconeEdgeAction c e
  let a := coconeEdgeActionTransport c e
  let t := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorEdge a).toTruncated
  let i := SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom K).obj X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)
  have h : homMk i ≫
      homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex d)).toTruncated =
    homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex c)).toTruncated ≫
      homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeTop c d t).toTruncated := by
    rw [homMk_id, Category.id_comp]
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeCoconeFunctorEdge_unit_square a
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homMk_square_transport i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex d)).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex c)).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeWholeEdgeTop c d t).toTruncated i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeTransformationPointAt d
      (coconeEdgeAction_vertex c e))).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationVertex c)).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantFunctorEdge (A := K) e.toTruncated) h rfl rfl rfl
    (congrArg (fun z => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const z : K ⟶ X)) (coconeEdgeAction_vertex c e))
    rfl (coconeTransformationPointAt_edge d (coconeEdgeAction_vertex c e)).symm
    rfl (coconeEdgeActionTransport_top c e)
  simpa only [i, homMk_id, Category.id_comp] using H

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
