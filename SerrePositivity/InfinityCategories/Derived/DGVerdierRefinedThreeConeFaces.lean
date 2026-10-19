module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierTwoSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Derived.DGVerdierRefinedThreeSimplex
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementCongruence

/-! # 細分後の実分母三単体の三面は同じ細分辺錐

概要：回収三単体の三つの錐面を、元の指定辺錐の同じ閉始点細分へ厳密に同定する。
方針：元の正番号面の四面体と始対象を照合し、一般閉始点細分の合同性を使う。
規約：元の零面・追加実閉辺を保持。使われ方：有限二次図式の共通面の組み立て。
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


/-- 元のホーンの各正番号面は、指定辺錐の回収四面体そのもの。 -/
lemma dgVerdierTriangleCanonicalFace_cone (i : Fin 3) :
    dgFourLastHornCanonicalFace (dgVerdierDiagramTriangleHorn A D C σ H)
      i.succ.castSucc (Fin.castSucc_ne_last _) =
      SSet.yonedaEquiv (roofPointSliceTetrahedron _ (H i).simplex.val) :=
  (dgFourLastHornCanonicalFace_eq (dgVerdierDiagramTriangleHorn A D C σ H)
    i.succ.castSucc (Fin.castSucc_ne_last _)).trans
      ((SSet.yonedaEquiv_comp (horn.ι (4 : Fin 5) i.succ.castSucc (Fin.castSucc_ne_last _))
        (dgVerdierDiagramTriangleHorn A D C σ H)).symm.trans
          (congrArg (SSet.yonedaEquiv (X := dgNerve A D))
            (dgVerdierDiagramTriangleHorn_face_cone A D C σ H i)))

/-- 指定辺錐の回収四面体の始対象は、同じ元のホーンの回収始対象。 -/
lemma dgVerdierTriangleConeTetrahedron_source (i : Fin 3) :
    (HornData.knownData (dgVerdierDiagramTriangleHorn A D C σ H)).obj 0 =
      (SSet.yonedaEquiv (roofPointSliceTetrahedron _ (H i).simplex.val)).obj 0 := by
  fin_cases i
  · exact congrArg (fun t : Simplex A D 3 => t.obj 0)
      (dgVerdierTriangleCanonicalFace_cone A D C σ H 0)
  · exact congrArg (fun t : Simplex A D 3 => t.obj 0)
      (dgVerdierTriangleCanonicalFace_cone A D C σ H 1)
  · exact congrArg (fun t : Simplex A D 3 => t.obj 0)
      (dgVerdierTriangleCanonicalFace_cone A D C σ H 2)

variable [Small.{u} D] [IsDGPretriangulated A D]
variable (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
  ((HornData.knownData (dgVerdierDiagramTriangleHorn A D C σ H)).obj 0))
variable (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P)

/-- 元の各指定辺錐を、同じ追加実閉辺で始点細分した実分母二単体。 -/
def dgVerdierDiagramRefinedEdgeCone (i : Fin 3) : (dgVerdierOver A D P x : SSet) _⦋2⦌ :=
  dgVerdierTwoSimplexInitialRefinement A D P x (H i).simplex q
    (dgClosedTargetTransport A D s (dgVerdierTriangleConeTetrahedron_source A D C σ H i))
    (dgClosedTargetTransport_mem A D P s
      (dgVerdierTriangleConeTetrahedron_source A D C σ H i) hs)

/-- 細分後の実分母三単体の各正番号面は、同じ閉射で細分した元の指定辺錐。 -/
lemma dgVerdierDiagramRefinedThreeSimplex_face_cone (F : Δ[4] ⟶ dgNerve A D)
    (hF : (horn 4 4).ι ≫ F =
      dgFourLastHornSourceRefinement (dgVerdierDiagramTriangleHorn A D C σ H) q s)
    (i : Fin 3) :
    (dgVerdierOver A D P x : SSet).δ i.succ
      (dgVerdierDiagramRefinedThreeSimplex A D C σ H q s hs F hF) =
        dgVerdierDiagramRefinedEdgeCone A D C σ H q s hs i := by
  apply Subtype.ext
  apply roofPointSliceTetrahedron_injective
    ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))
  have hc := dgSimplexInitialRefinement_congr
    (dgVerdierTriangleCanonicalFace_cone A D C σ H i) q q s
    (dgClosedTargetTransport A D s (dgVerdierTriangleConeTetrahedron_source A D C σ H i))
    (dgClosedTargetTransport_edge A D s _).symm
  have hr := dgVerdierTwoSimplexInitialRefinement_tetrahedron A D P x (H i).simplex q
    (dgClosedTargetTransport A D s (dgVerdierTriangleConeTetrahedron_source A D C σ H i))
    (dgClosedTargetTransport_mem A D P s
      (dgVerdierTriangleConeTetrahedron_source A D C σ H i) hs)
  fin_cases i
  · exact (dgVerdierDiagramRefinedOverThreeSimplex_face1 A D C σ H q s F hF).trans
      ((congrArg (SSet.yonedaEquiv (X := dgNerve A D)).symm hc).trans hr.symm)
  · exact (dgVerdierDiagramRefinedOverThreeSimplex_face2 A D C σ H q s F hF).trans
      ((congrArg (SSet.yonedaEquiv (X := dgNerve A D)).symm hc).trans hr.symm)
  · exact (dgVerdierDiagramRefinedOverThreeSimplex_face3 A D C σ H q s F hF).trans
      ((congrArg (SSet.yonedaEquiv (X := dgNerve A D)).symm hc).trans hr.symm)

end SerrePositivity.InfinityCategories
