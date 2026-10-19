module
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornFinalSimplex
public import SerrePositivity.InfinityCategories.Derived.DGVerdierDiagramTriangleHorn
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOverVertexInverse

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}
variable (C : DGVerdierDiagramVertexCone A D P x f) (σ : K _⦋2⦌)
variable (H : ∀ i : Fin 3, Truncated.Edge.CompStruct
  (C.leg (K.δ 1 (K.δ i σ)))
  ((edgeOfSimplex (K.δ i σ)).map ((truncation 2).map f))
  (C.leg (K.δ 0 (K.δ i σ))))

/-- 四次ホーンから回収した最後の閉辺は、元の指定二単体の終頂点の分母辺。 -/
lemma dgVerdierDiagramTriangleLastClosed_edge :
    (dgClosedEdge A D (dgFourLastHornFinalClosed
      (dgVerdierDiagramTriangleHorn A D C σ H))).edge =
      (roofPointSliceVertexEdge
        ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))
        ((dgVerdierOver A D P x : SSet).δ 0
          ((dgVerdierOver A D P x : SSet).δ 0 (f.app _ σ))).val).edge := by
  let a := (SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x)
  let F := dgVerdierDiagramTriangleHorn A D C σ H
  let t := (f.app _ σ).val
  have hface : F.app (Opposite.op ⦋3⦌) (horn.face 4 0 (by decide)) =
      (SSet.yonedaEquiv (X := dgNerve A D)) (roofPointSliceTetrahedron a t) :=
    (SSet.yonedaEquiv_comp (horn.ι (4 : Fin 5) 0 (by decide)) F).symm.trans
      (congrArg (SSet.yonedaEquiv (X := dgNerve A D))
        (dgVerdierDiagramTriangleHorn_face0 A D C σ H))
  have hfirst : (dgNerve A D).δ 0 (SSet.yonedaEquiv (roofPointSliceTetrahedron a t)) =
      SSet.yonedaEquiv (roofPointSliceTriangle a ((sliceOver a).δ 0 t)) :=
    (SSet.stdSimplex.yonedaEquiv_δ_comp (roofPointSliceTetrahedron a t) 0).symm.trans
      (congrArg (SSet.yonedaEquiv (X := dgNerve A D))
        (roofPointSliceTetrahedron_face a t 0))
  have hlast : (dgNerve A D).δ 0 ((dgNerve A D).δ 0
      (SSet.yonedaEquiv (roofPointSliceTetrahedron a t))) =
      (roofPointSliceVertexEdge a ((sliceOver a).δ 0 ((sliceOver a).δ 0 t))).edge :=
    (congrArg (fun s : Simplex A D 2 => (dgNerve A D).δ 0 s) hfirst).trans
      ((SSet.stdSimplex.yonedaEquiv_δ_comp
        (roofPointSliceTriangle a ((sliceOver a).δ 0 t)) 0).symm.trans
          (roofPointSliceTriangle_leg a ((sliceOver a).δ 0 t) 0))
  exact ((dgFourLastHornFinalClosed_edge F).trans
    (dgFourLastHornFinalSimplex_eq_faces F)).trans
    ((congrArg (fun s : Simplex A D 3 => (dgNerve A D).δ 0 ((dgNerve A D).δ 0 s))
      hface).trans hlast)

/-- 四次ホーンの最後の回収閉射は、元の指定集合の実 Verdier 分母。 -/
lemma dgVerdierDiagramTriangleLastClosed_mem :
    (dgClosedEdge A D (dgFourLastHornFinalClosed
      (dgVerdierDiagramTriangleHorn A D C σ H))).edge ∈ dgVerdierEdges A D P :=
  (congrArg (fun z => z ∈ dgVerdierEdges A D P)
    (dgVerdierDiagramTriangleLastClosed_edge A D C σ H)).mpr
      (dgVerdierOverVertex_mem A D P x
        ((dgVerdierOver A D P x : SSet).δ 0 ((dgVerdierOver A D P x : SSet).δ 0 (f.app _ σ))))

end SerrePositivity.InfinityCategories
