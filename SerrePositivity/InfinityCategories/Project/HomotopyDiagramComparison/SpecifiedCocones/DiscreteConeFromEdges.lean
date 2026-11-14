module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FiniteShapes

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.FiniteShapes.LiftedDiscreteVertexMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeLeg

/-!
概要：元の離散図式の各値へ向かう指定辺から、頂点と全脚を保持する全錐を構成する。
方針：各辺を頂点下の coslice に入れ、元の離散図式として束ねて uncurry する。
規約：充填性・有限性は不要。元の全一単体を変更しない。
使われ方：有限 coherent 積の射影変換から関手圏内の全錐を作る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の辺を、元の始点下の coslice の頂点として表示する。 -/
def edgeSourceCosliceVertex {X : SSet.{u + 1}} {z y : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) z y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm z)) _⦋0⦌ :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm f.edge, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_source]⟩

variable {J : Type u} {X : SSet.{u + 1}}
  (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J)) ⟶ X)
  {z : X _⦋0⦌}
  (f : (j : J) → SSet.Truncated.Edge (X := (truncation 2).obj X) z
    (p.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j)))))

/-- 元の全脚を同じ頂点下の coslice 内の全離散図式にまとめる。 -/
def discreteEdgeConeFamily :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm z) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteVertexMap (fun j ↦ edgeSourceCosliceVertex (f j))

/-- 元の各頂点での全脚族の値は、同じ元の脚の coslice 頂点。 -/
lemma discreteEdgeConeFamily_vertex (j : J) :
    (discreteEdgeConeFamily p f).app (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j))) = edgeSourceCosliceVertex (f j) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteVertexMap_vertex _ _

/-- 元の脚族の一点制限は、元の脚の coslice 頂点を表す射そのもの。 -/
lemma discreteEdgeConeFamily_at (j : J) :
    SSet.yonedaEquiv.symm (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j))) ≫
      discreteEdgeConeFamily p f = SSet.yonedaEquiv.symm (edgeSourceCosliceVertex (f j)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, discreteEdgeConeFamily_vertex,
    Equiv.apply_symm_apply]

/-- 元の離散図式と指定された全脚から、元の頂点を持つ全錐を構成する。 -/
def discreteConeFromEdges : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (discreteEdgeConeFamily p f), by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection]
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteDiagram_ext
    intro j
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm z)).app _
      ((discreteEdgeConeFamily p f).app _ _) = _
    rw [discreteEdgeConeFamily_vertex]
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm (f j.as).edge)) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inr, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target,
      Equiv.apply_symm_apply]⟩

/-- 元の全錐の頂点は、指定した元の頂点そのもの。 -/
lemma discreteConeFromEdges_vertex : (discreteConeFromEdges p f).vertex = z := by
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (discreteEdgeConeFamily p f)) = z
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed, Equiv.apply_symm_apply]

/-- 元の全錐の各脚は、元の指定辺の全一単体を厳密に保持する。 -/
lemma discreteConeFromEdges_leg_edge (j : J) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (discreteConeFromEdges p f)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j)))).edge = (f j).edge := by
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion _ ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (discreteEdgeConeFamily p f)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp,
    discreteEdgeConeFamily_at, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda]
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm (f j).edge)) = _
  rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
