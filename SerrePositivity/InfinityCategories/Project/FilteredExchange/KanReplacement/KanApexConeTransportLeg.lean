module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaces
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeHomotopyEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.EdgeSquareTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeLeg
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.EdgeApexPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanApexConeTransportEdges
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanNativeConeLeg
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.SpaceHomotopyClasses
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.SpecifiedApexLimitConeTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：元の Kan 射による頂点輸送の各脚を、元の射と比較先の脚の合成へ比較する。
方針：全錐の自然性の四辺を実際の coherent 辺へ移し、図式の恒等辺を消去する。
規約：元の射と二つの頂点を保持。使われ方：一般 coherent filtered 余極限後の脚。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {I : Type u} [SmallCategory I] {D : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
  (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve D))
  {K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (a : K ⟶ L) {v : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌}
  (t : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.SpecifiedApexLimitConeTransport d (SSet.yonedaEquiv.symm v)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.edgeApexPrism (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a)))
  (hv : v = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex K)

/-- 元の始域を頂点とする輸送後の脚を、同じ Kan 対象間の射へ戻す。 -/
def kanApexConeTransportLeg (i : I) : K ⟶ D.obj i :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg t.cone K (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanApexConeTransport_vertex d a t hv) i

/-- 輸送後の脚は、元の比較射と元の比較先の脚の合成にホモトピック。 -/
lemma kanApexConeTransportLeg_comparison (hd : d.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex L) (i : I) :
    Nonempty (SSet.Homotopy (kanApexConeTransportLeg d a t hv i)
      (a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg d L hd i)) := by
  let j := ULift.up.{u + 1} (ComposableArrows.mk₀ i)
  let V := D.obj i
  have hdi := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_vertex D i).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent _)
  have hr : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyDiagramEdge t.homotopy j).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (𝟙 V)).edge := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanApexConeTransport_diagramEdge]
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex V) 1 :=
        congrArg (fun x => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) hdi
      _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]; rfl
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homMk_square_transport (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg t.cone j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyDiagramEdge t.homotopy j) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyApexEdge t.homotopy)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg d j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (kanApexConeTransportLeg d a t hv i)).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (𝟙 V)).toTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg d L hd i)).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopy_leg_naturality t.homotopy j)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanApexConeTransport_vertex d a t hv) hdi hd hdi
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg_edge _ _ _ i).symm hr (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanApexConeTransport_apexEdge d a t)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg_edge d L hd i).symm
  have hid : SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (𝟙 V)).toTruncated = 𝟙 _ := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_id, SSet.Edge.toTruncated_id,
      SSet.Truncated.HomotopyCategory.homMk_id]
  rw [hid, Category.comp_id] at hs
  apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinity_homotopy_of_homMk_eq
  exact hs.trans (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct a (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg d L hd i)).toTruncated)

end SerrePositivity.InfinityCategories.Project.FilteredExchange
