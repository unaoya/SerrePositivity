module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGLastHornFinalSimplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGVerdierDiagramEdgeHorn
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierOverVertexInverse

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] (P : Set D) (x : D)
variable {d s t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}) _⦋0⦌}
variable (u : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet)) d s)
variable (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet)) s t)
variable (w : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet)) d t)

/-- 回収した最後の閉辺の一次単体は、元の指定終端 over 頂点の分母辺そのもの。 -/
lemma dgVerdierConeLastClosed_edge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeEdgeHorn A D P x u e w))).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) t.val).edge := by
  let a := (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)
  let H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeEdgeHorn A D P x u e w
  let E := e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x).ι)
  have hface : H.app (Opposite.op ⦋2⦌) (horn.face 3 0 (by decide)) =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a E.edge) :=
    (SSet.yonedaEquiv_comp (horn.ι (3 : Fin 4) 0 (by decide)) H).symm.trans
      (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeEdgeHorn_face0 A D P x u e w))
  have hfinal : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalSimplex H = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a t.val).edge :=
    (congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ (0 : Fin 3)) hface).trans
      ((SSet.stdSimplex.yonedaEquiv_δ_comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a E.edge) 0).symm.trans
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_leg a E.edge 0).trans
          (congrArg (fun v => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a v).edge) E.tgt_eq)))
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed_edge H).trans hfinal

/-- 回収した最後の元の閉零射は、実 Verdier 分母である。 -/
lemma dgVerdierConeLastClosed_mem :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeEdgeHorn A D P x u e w))).edge ∈
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P :=
  (congrArg (fun z => z ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)
    (dgVerdierConeLastClosed_edge A D P x u e w)).mpr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverVertex_mem A D P x t)

variable [Small.{u} D] {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}

omit [Small.{u} D] in
/-- 有限図式の指定辺の二未知式から回収した最後の閉射も、元の実 Verdier 分母。 -/
lemma dgVerdierDiagramLastClosed_mem (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f)
    (a : K _⦋1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornFinalClosed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C a))).edge ∈
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P :=
  dgVerdierConeLastClosed_mem A D P x (C.leg (K.δ 1 a))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a).map ((truncation 2).map f)) (C.leg (K.δ 0 a))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
