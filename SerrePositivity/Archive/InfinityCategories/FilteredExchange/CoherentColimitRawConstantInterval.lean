module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawInterval
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CompositionTriangleFaces

/-!
概要：元の指定余極限辺の区間頂点への定値族は、同じ元の実一次単体の係数引き戻し。
方針：区間頂点と実辺の厳密な往復を全係数で使う。
規約：元の辺と区間頂点を保持。使われ方：全第一辺選択上の同じ長区間の全輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の実辺の区間頂点を全係数へ定値にしても、同じ元の実辺を回収する。 -/
lemma intervalMappingUncurry_const_edge {X L : SSet.{u}} {x y : X _⦋0⦌}
    (e : X.Edge x y) :
    intervalMappingUncurry (SSet.const (intervalMappingVertexOfEdge e) : L ⟶ _) =
      fst (Δ[1] : SSet.{u}) L ≫ SSet.yonedaEquiv.symm e.edge := by
  rw [intervalMappingUncurry_const_vertex]
  exact congrArg (fun t : X.Edge x y => fst (Δ[1] : SSet.{u}) L ≫ SSet.yonedaEquiv.symm t.edge)
    ((intervalMappingEdgeVertexEquiv x y).symm_apply_apply e)

/-- 元の余極限区間頂点の全定値族は、元の同じ指定余極限辺を全係数で引き戻したもの。 -/
lemma coherentColimitRawConstantInterval_uncurry (B : SSet.{u})
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (a : SSet.Homotopy F G) (L : SSet.{u + 1}) :
    intervalMappingUncurry (SSet.const (coherentColimitRawIntervalVertex B a) : L ⟶ _) =
      fst (Δ[1] : SSet.{u + 1}) L ≫
        SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B a).edge :=
  intervalMappingUncurry_const_edge _

end SerrePositivity.InfinityCategories.F2
