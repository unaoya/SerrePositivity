module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGFourLastHornFinalSimplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGVerdierDiagramTriangleHorn
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierOverVertexInverse

/-! # 実図式二単体から回収する四次ホーン最後辺の実分母性

概要：回収された最後の閉射は、元の実二単体の終頂点の分母辺と厳密に一致する。
方針：指定零面から最後の二面を取り、over の四面体・三角形の回収公式を接続する。
規約：元の実辺の厳密一致。使われ方：高次残差 cone の有限 cell 性と追加分母消去。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f) (σ : K _⦋2⦌)
variable (H : ∀ i : Fin 3, Truncated.Edge.CompStruct
  (C.leg (K.δ 1 (K.δ i σ)))
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (K.δ i σ)).map ((truncation 2).map f))
  (C.leg (K.δ 0 (K.δ i σ))))

/-- 四次ホーンから回収した最後の閉辺は、元の指定二単体の終頂点の分母辺。 -/
lemma dgVerdierDiagramTriangleLastClosed_edge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFinalClosed
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H))).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0 (f.app _ σ))).val).edge := by
  let a := (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H
  let t := (f.app _ σ).val
  have hface : F.app (Opposite.op ⦋3⦌) (horn.face 4 0 (by decide)) =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a t) :=
    (SSet.yonedaEquiv_comp (horn.ι (4 : Fin 5) 0 (by decide)) F).symm.trans
      (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn_face0 A D C σ H))
  have hfirst : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 0 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a t)) =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ 0 t)) :=
    (SSet.stdSimplex.yonedaEquiv_δ_comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a t) 0).symm.trans
      (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_face a t 0))
  have hlast : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 0 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 0
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron a t))) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ 0 ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ 0 t))).edge :=
    (congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2 => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 0 s) hfirst).trans
      ((SSet.stdSimplex.yonedaEquiv_δ_comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ 0 t)) 0).symm.trans
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_leg a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ 0 t) 0))
  exact ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFinalClosed_edge F).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFinalSimplex_eq_faces F)).trans
    ((congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 3 => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 0 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 0 s))
      hface).trans hlast)

/-- 四次ホーンの最後の回収閉射は、元の指定集合の実 Verdier 分母。 -/
lemma dgVerdierDiagramTriangleLastClosed_mem :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFinalClosed
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H))).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P :=
  (congrArg (fun z => z ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)
    (dgVerdierDiagramTriangleLastClosed_edge A D C σ H)).mpr
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverVertex_mem A D P x
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0 ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0 (f.app _ σ))))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
