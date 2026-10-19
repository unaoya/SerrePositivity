module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornFinalSimplex
public import SerrePositivity.InfinityCategories.Derived.DGVerdierDiagramEdgeHorn
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOverVertexInverse

/-! # 回収した最後の閉辺の実 Verdier 分母性

概要：実分母の図式辺と二脚から回収した最後の閉射は、元の指定分母の実辺を持つ。
方針：零面の厳密一致から最後の辺を回収し、実 over 頂点の分母条件を移す。
規約：H⁰ の同値だけに弱めない。使われ方：二未知残差を閉辺の cone 内へ入れる前提。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (P : Set D) (x : D)
variable {d s t : (dgVerdierOver A D P x : SSet.{max u v}) _⦋0⦌}
variable (u : Truncated.Edge (X := (truncation 2).obj (dgVerdierOver A D P x : SSet)) d s)
variable (e : Truncated.Edge (X := (truncation 2).obj (dgVerdierOver A D P x : SSet)) s t)
variable (w : Truncated.Edge (X := (truncation 2).obj (dgVerdierOver A D P x : SSet)) d t)

/-- 回収した最後の閉辺の一次単体は、元の指定終端 over 頂点の分母辺そのもの。 -/
lemma dgVerdierConeLastClosed_edge :
    (dgClosedEdge A D (dgLastHornFinalClosed (dgVerdierConeEdgeHorn A D P x u e w))).edge =
      (roofPointSliceVertexEdge
        ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x)) t.val).edge := by
  let a := (SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x)
  let H := dgVerdierConeEdgeHorn A D P x u e w
  let E := e.map ((truncation 2).map (dgVerdierOver A D P x).ι)
  have hface : H.app (Opposite.op ⦋2⦌) (horn.face 3 0 (by decide)) =
      (SSet.yonedaEquiv (X := dgNerve A D)) (roofPointSliceTriangle a E.edge) :=
    (SSet.yonedaEquiv_comp (horn.ι (3 : Fin 4) 0 (by decide)) H).symm.trans
      (congrArg (SSet.yonedaEquiv (X := dgNerve A D))
        (dgVerdierConeEdgeHorn_face0 A D P x u e w))
  have hfinal : dgLastHornFinalSimplex H = (roofPointSliceVertexEdge a t.val).edge :=
    (congrArg ((dgNerve A D).δ (0 : Fin 3)) hface).trans
      ((SSet.stdSimplex.yonedaEquiv_δ_comp (roofPointSliceTriangle a E.edge) 0).symm.trans
        ((roofPointSliceTriangle_leg a E.edge 0).trans
          (congrArg (fun v => (roofPointSliceVertexEdge a v).edge) E.tgt_eq)))
  exact (dgLastHornFinalClosed_edge H).trans hfinal

/-- 回収した最後の元の閉零射は、実 Verdier 分母である。 -/
lemma dgVerdierConeLastClosed_mem :
    (dgClosedEdge A D (dgLastHornFinalClosed (dgVerdierConeEdgeHorn A D P x u e w))).edge ∈
      dgVerdierEdges A D P :=
  (congrArg (fun z => z ∈ dgVerdierEdges A D P)
    (dgVerdierConeLastClosed_edge A D P x u e w)).mpr (dgVerdierOverVertex_mem A D P x t)

variable [Small.{u} D] {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}

omit [Small.{u} D] in
/-- 有限図式の指定辺の二未知式から回収した最後の閉射も、元の実 Verdier 分母。 -/
lemma dgVerdierDiagramLastClosed_mem (C : DGVerdierDiagramVertexCone A D P x f)
    (a : K _⦋1⦌) :
    (dgClosedEdge A D (dgLastHornFinalClosed (dgVerdierDiagramEdgeHorn A D C a))).edge ∈
      dgVerdierEdges A D P :=
  dgVerdierConeLastClosed_mem A D P x (C.leg (K.δ 1 a))
    ((edgeOfSimplex a).map ((truncation 2).map f)) (C.leg (K.δ 0 a))

end SerrePositivity.InfinityCategories
