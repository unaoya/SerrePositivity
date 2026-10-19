module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierDiagramHornSource

/-! # 実分母頂点図式の各脚の実三角形と共通端点

概要：各頂点脚の over 三角形を固定し、図式辺ホーンの二面が同じ脚の三角形と一致する。
方針：over 始脚の式で対角分母と両端点を回収し、ホーン指定面の厳密等式を使う。
規約：脚の三角形を図式辺から独立に固定する。使われ方：有限同時細分の脚の辺間一致。
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
variable (C : DGVerdierDiagramVertexCone A D P x f)

/-- 各頂点脚に付随する実三角形を、図式辺から独立に固定する。 -/
def dgVerdierDiagramLegTriangle (v : K _⦋0⦌) : Simplex A D 2 :=
  (SSet.yonedaEquiv (X := dgNerve A D))
    (roofPointSliceTriangle ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))
      (((C.leg v).map ((truncation 2).map (dgVerdierOver A D P x).ι)).edge))

/-- 各脚三角形の対角辺は元の同じ共通閉分母の実辺。 -/
lemma dgVerdierDiagramLegTriangle_diagonal (v : K _⦋0⦌) :
    (dgNerve A D).δ 1 (dgVerdierDiagramLegTriangle A D C v) =
      (dgClosedEdge A D C.denominator.obj.hom).edge := by
  let a := (SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x)
  let E := (C.leg v).map ((truncation 2).map (dgVerdierOver A D P x).ι)
  exact (SSet.stdSimplex.yonedaEquiv_δ_comp (roofPointSliceTriangle a E.edge) 1).symm.trans
    ((roofPointSliceTriangle_leg a E.edge 1).trans
      ((congrArg (fun v => (roofPointSliceVertexEdge a v).edge) E.src_eq).trans
        (dgClosedOverVertex_edge A D C.denominator.obj.hom)))

/-- 各脚三角形の零面は、その元の指定終頂点の分母辺。 -/
lemma dgVerdierDiagramLegTriangle_face0 (v : K _⦋0⦌) :
    (dgNerve A D).δ 0 (dgVerdierDiagramLegTriangle A D C v) =
      (roofPointSliceVertexEdge
        ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x)) (f.app _ v).val).edge := by
  let a := (SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x)
  let E := (C.leg v).map ((truncation 2).map (dgVerdierOver A D P x).ι)
  exact (SSet.stdSimplex.yonedaEquiv_δ_comp (roofPointSliceTriangle a E.edge) 0).symm.trans
    ((roofPointSliceTriangle_leg a E.edge 0).trans
      (congrArg (fun v => (roofPointSliceVertexEdge a v).edge) E.tgt_eq))

/-- 各脚三角形の始対象は、元の共通閉分母の同じ始対象。 -/
lemma dgVerdierDiagramLegTriangle_source (v : K _⦋0⦌) :
    (dgVerdierDiagramLegTriangle A D C v).obj 0 =
      ForgetEnrichment.to (Complex A) C.denominator.obj.left :=
  congrArg (fun t : Simplex A D 1 => t.obj 0) (dgVerdierDiagramLegTriangle_diagonal A D C v)

/-- 各脚三角形の終対象は、同じ指定対象 x。 -/
lemma dgVerdierDiagramLegTriangle_target (v : K _⦋0⦌) :
    (dgVerdierDiagramLegTriangle A D C v).obj 2 = x :=
  congrArg (fun t : Simplex A D 1 => t.obj 1) (dgVerdierDiagramLegTriangle_diagonal A D C v)

/-- 各辺ホーンの面 023 は、その終頂点の同じ固定脚三角形。 -/
lemma dgVerdierDiagramCanonicalFace1_leg (e : K _⦋1⦌) :
    dgLastHornCanonicalFace (dgVerdierDiagramEdgeHorn A D C e) 1 (by decide) =
      dgVerdierDiagramLegTriangle A D C (K.δ 0 e) :=
  (dgLastHornCanonicalFace_eq (dgVerdierDiagramEdgeHorn A D C e) 1 (by decide)).trans
    ((SSet.yonedaEquiv_comp (horn.ι (3 : Fin 4) 1 (by decide))
      (dgVerdierDiagramEdgeHorn A D C e)).symm.trans
        (congrArg (SSet.yonedaEquiv (X := dgNerve A D))
          (dgVerdierConeEdgeHorn_face1 A D P x (C.leg (K.δ 1 e))
            ((edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)))))

/-- 各辺ホーンの面 013 は、その始頂点の同じ固定脚三角形。 -/
lemma dgVerdierDiagramCanonicalFace2_leg (e : K _⦋1⦌) :
    dgLastHornCanonicalFace (dgVerdierDiagramEdgeHorn A D C e) 2 (by decide) =
      dgVerdierDiagramLegTriangle A D C (K.δ 1 e) :=
  (dgLastHornCanonicalFace_eq (dgVerdierDiagramEdgeHorn A D C e) 2 (by decide)).trans
    ((SSet.yonedaEquiv_comp (horn.ι (3 : Fin 4) 2 (by decide))
      (dgVerdierDiagramEdgeHorn A D C e)).symm.trans
        (congrArg (SSet.yonedaEquiv (X := dgNerve A D))
          (dgVerdierConeEdgeHorn_face2 A D P x (C.leg (K.δ 1 e))
            ((edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)))))

end SerrePositivity.InfinityCategories
