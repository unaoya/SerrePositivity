module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeHomotopyDiagonalEdge
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeHomotopyEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeHomotopyLowerTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeHomotopyUpperTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeLeg
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanConeHomotopyDiagonal
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanNativeConeLeg
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.SpaceTriangleFaces

/-!
概要：Kan 図式上の全錐比較の上下の指定三角形を実際のホモトピーにする。
方針：元の三辺の厳密な同定と精密化の uncurry。
規約：両方で同じ対角射を使う。使われ方：各脚の指定比較と二次の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {I : Type u} [SmallCategory I] {F G : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
  {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F)} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve G)}
  (T : SSet.Homotopy c.val d.val) (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
  (hc : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex K) (hd : d.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex L)

/-- 概要：下側の指定三角形は対角と元の脚・図式成分の合成のホモトピー。
方針：全錐円柱の元の二単体を読み戻す。
規約：元の三角形を保持。使われ方：各脚の指定比較の始域側。 -/
def kanConeHomotopyLower (i : I) (r : F.obj i ⟶ G.obj i)
    (hr : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyDiagramEdge T (ULift.up (ComposableArrows.mk₀ i))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge r).edge) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanConeHomotopyDiagonal T K hc i) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg c K hc i ≫ r) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityTriangleHomotopy_of_faces _ _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyLowerTriangle T (ULift.up (ComposableArrows.mk₀ i)))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyLowerTriangle_two T _).trans (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg_edge c K hc i).symm)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyLowerTriangle_zero T _).trans hr)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyLowerTriangle_one T _).trans (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanConeHomotopyDiagonal_edge T K hc i).symm)

/-- 概要：上側の指定三角形は対角と頂点比較・比較先の脚の合成のホモトピー。
方針：全錐円柱の元の二単体を読み戻す。
規約：下側と同じ対角射。使われ方：各脚の指定比較の終域側。 -/
def kanConeHomotopyUpper (i : I) (a : K ⟶ L)
    (ha : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyApexEdge T).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a).edge) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanConeHomotopyDiagonal T K hc i) (a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg d L hd i) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityTriangleHomotopy_of_faces _ _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyUpperTriangle T (ULift.up (ComposableArrows.mk₀ i)))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyUpperTriangle_two T _).trans ha)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyUpperTriangle_zero T _).trans (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg_edge d L hd i).symm)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyUpperTriangle_one T _).trans (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanConeHomotopyDiagonal_edge T K hc i).symm)

end SerrePositivity.InfinityCategories.Project.FilteredExchange
