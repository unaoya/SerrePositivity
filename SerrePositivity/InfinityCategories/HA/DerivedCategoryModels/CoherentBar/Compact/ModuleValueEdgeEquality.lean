module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ModuleValueNaturality
/-!
概要：表示を輸送した実加群作用を、元の dg 閉辺の native 作用へ厳密に同定する。
方針：全一単体の等式から空間辺の実作用の異種等式を得る。
規約：元の実辺と基礎空間関手を変更しない。
使われ方：bar 余錐の実脚に全基点コホモロジー自然性を適用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial

lemma dgBarCompactSpaceEdgeValue_heq {x y x' y' : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}.Edge x y) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}.Edge x' y')
    (h : e.edge = e'.edge) : HEq (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue e) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue e') := by
  have hx : x = x' := e.src_eq.symm.trans ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}.δ 1) h).trans e'.src_eq)
  have hy : y = y' := e.tgt_eq.symm.trans ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}.δ 0) h).trans e'.tgt_eq)
  subst x'; subst y'
  have he : e = e' := SSet.Edge.ext h
  subst e'
  rfl

variable (R : Type u) [CommRing R] (D : Type v)

/-- 同じ閉射の元の dg 閉辺を、そのまま native 基礎空間へ写した作用。 -/
def dgBarCompactModuleValueNativeEdge {M N : ModuleCategory R PUnit.{1}} (f : M ⟶ N) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue
    ((SSet.Edge.ofTruncated
      (X := (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleNerve R D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v + 1}
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).onClosed.map f)))).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R D))

lemma dgBarCompactModuleValueEdge_eq_native
    {M N : ModuleCategory R PUnit.{1}} (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleValueEdge R D f = dgBarCompactModuleValueNativeEdge R D f := by
  have hu : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCoherentUnderlyingValueFunctor R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R D := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCoherentUnderlyingValueFunctor]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentNerveVertex_eq_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison_vertex,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactUnderlyingValueFunctor_unit]
  have hraw : HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModuleRawValueEdge R D f)
      (dgBarCompactModuleValueNativeEdge R D f) := by
    apply dgBarCompactSpaceEdgeValue_heq
    change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCoherentUnderlyingValueFunctor R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D)).app (Opposite.op ⦋1⦌)
          (ULift.up (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
            ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).onClosed.map f)).map
              (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R))).edge)) = _
    rw [hu, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentComparison_closed_edge]
    rfl
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSpaceMapCast_heq _ _ _).trans hraw)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
