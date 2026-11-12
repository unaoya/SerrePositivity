module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.KanPointSurjectivity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanPointComponentComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointedSpaceHomPoint
public import SerrePositivity.KST.Fibration.PointedLeftResolutionVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceFiberHomClass
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedReverseCompositionTransport
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyOpposite
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.UniverseVertexIso

/-! # Kan 写像の本質的全射性を、同じ点の射の全射性から回収する

実 pointed fiber の同型と、既存の全写像空間の同値による逆像を使う。
高次写像空間の充満忠実性を零次の主張で代用しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration
/-- 座標変更後の同じ比較は、元の指定した Kan 点の標準 pointed 表示を回収。 -/
theorem kanPointFiberComparison_vertex (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (v : K.obj _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanPointFiberComparison K).app (Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm (ULift.up v)) = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv K).symm v := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv K).injective
  exact (pointedReverseKanFiberComparison_point K v).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv K).apply_symm_apply v).symm

/-- 同じ Kan 値で点の射の類が一致すれば、元の二点は実際に同型。 -/
def kanVertexIsoOfPointHomEq (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) {v w : K.obj _⦋0⦌}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv K).symm v) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv K).symm w)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := K.obj) v w := by
  let e := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanPointFiberComparison_isFullyFaithful K).preimageVertexIso
    (eqToIso (congrArg HomotopyCategory.mk (kanPointFiberComparison_vertex K v)) ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceFiberVertexIsoOfHomEq h ≪≫
        (eqToIso (congrArg HomotopyCategory.mk (kanPointFiberComparison_vertex K w))).symm)
  let t := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.homotopyOppositeEquivalence
    ((SSet.uliftFunctor.{u + 1, u}).obj K.obj)).functor.mapIso e
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.downVertexIso t.unop.symm

/-- 元の成分辺が全ての点の射を覆うなら、同じ Kan 写像は本質的全射。 -/
theorem kanMap_isEssentiallySurjective_of_point_surjective {K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (f : K ⟶ L)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex K) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex L))
    (he : e.edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)
    (hs : Function.Surjective (fun a : HomotopyCategory.mk _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointSpaceVertex ⟶
        HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex K) =>
      a ≫ Truncated.HomotopyCategory.homMk e.toTruncated)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective f := by
  intro y
  obtain ⟨a, ha⟩ := hs (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv L).symm y))
  let w := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedSpaceFiberPointOfHom a
  let x := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv K w
  have hx : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv K).symm x = w :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv K).symm_apply_apply w
  refine ⟨x, ⟨kanVertexIsoOfPointHomEq L ?_⟩⟩
  have hp := (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom hx).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedSpaceFiberPointOfHom_hom a)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanPointHom_comp_of_edge f e he x).symm.trans
    ((congrArg (fun m => m ≫ Truncated.HomotopyCategory.homMk e.toTruncated) hp).trans ha)

end SerrePositivity.KST.Fibration
