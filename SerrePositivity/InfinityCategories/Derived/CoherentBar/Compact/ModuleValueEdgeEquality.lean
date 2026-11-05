module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ModuleValueNaturality
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DoldKanComparison SSet
open scoped _root_.Simplicial

lemma dgBarCompactSpaceEdgeValue_heq {x y x' y' : SpaceInfinity.{u} _⦋0⦌}
    (e : SpaceInfinity.{u}.Edge x y) (e' : SpaceInfinity.{u}.Edge x' y')
    (h : e.edge = e'.edge) : HEq (F2.spaceInfinityEdgeValue e) (F2.spaceInfinityEdgeValue e') := by
  have hx : x = x' := e.src_eq.symm.trans ((congrArg (SpaceInfinity.{u}.δ 1) h).trans e'.src_eq)
  have hy : y = y' := e.tgt_eq.symm.trans ((congrArg (SpaceInfinity.{u}.δ 0) h).trans e'.tgt_eq)
  subst x'; subst y'
  have he : e = e' := SSet.Edge.ext h
  subst e'
  rfl

variable (R : Type u) [CommRing R] (D : Type v)

/-- 同じ閉射の元の dg 閉辺を、そのまま native 基礎空間へ写した作用。 -/
def dgBarCompactModuleValueNativeEdge {M N : ModuleCategory R PUnit.{1}} (f : M ⟶ N) :=
  F2.spaceInfinityEdgeValue
    ((SSet.Edge.ofTruncated
      (X := (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj (dgHomModuleNerve R D))
      (uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v + 1}
        (dgClosedEdge R (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
          ((dgUniverseLiftUp R (RightModule R PUnit.{1})).onClosed.map f)))).map
      (dgHomUnderlyingSpaceInfinity R D))

lemma dgBarCompactModuleValueEdge_eq_native
    {M N : ModuleCategory R PUnit.{1}} (f : M ⟶ N) :
    dgBarCompactModuleValueEdge R D f = dgBarCompactModuleValueNativeEdge R D f := by
  have hu : dgBarCompactCoherentUnderlyingValueFunctor R
      (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (dgHomModuleUnit R D) = dgHomUnderlyingSpaceInfinity R D := by
    dsimp only [dgBarCompactCoherentUnderlyingValueFunctor]
    rw [coherentNerveVertex_eq_vertex, coherentComparison_vertex,
      dgBarCompactUnderlyingValueFunctor_unit]
  have hraw : HEq (dgBarCompactModuleRawValueEdge R D f)
      (dgBarCompactModuleValueNativeEdge R D f) := by
    apply dgBarCompactSpaceEdgeValue_heq
    change (dgBarCompactCoherentUnderlyingValueFunctor R
      (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
        (dgHomModuleUnit R D)).app (Opposite.op ⦋1⦌)
          (ULift.up (((coherentNerveEdge
            ((dgUniverseLiftUp R (RightModule R PUnit.{1})).onClosed.map f)).map
              (coherentComparison (R := R))).edge)) = _
    rw [hu, dgCoherentComparison_closed_edge]
    rfl
  exact eq_of_heq ((dgBarCompactSpaceMapCast_heq _ _ _).trans hraw)

end SerrePositivity.InfinityCategories
