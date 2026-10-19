module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierClosedVertexLegs
public import SerrePositivity.InfinityCategories.Derived.DGVerdierEdgeConeSource
public import SerrePositivity.InfinityCategories.Derived.DGVerdierTwoSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Derived.DGOverTwoSimplexRefinedFaces

/-! # 同じ閉始点細分による実辺錐と固定頂点脚の合成二単体

概要：元の任意の辺錐を同じ閉分母で細分し、その二脚を頂点ごとの固定実脚へ同定する。
方針：正番号面の三角形を元の固定脚三角形の細分と比較し、over 辺の単射性を使う。
規約：同じ指定二単体の台を保つ。使われ方：有限高次図式の共通頂点錐と辺整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}
variable {C : DGVerdierDiagramVertexCone A D P x f}
variable (R : DGVerdierClosedVertexRefinement A D C)

variable (e : K _⦋1⦌)
variable (H : Truncated.Edge.CompStruct (C.leg (K.δ 1 e))
  ((edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)))

/-- 元の指定辺錐を、共通の同じ追加閉分母で細分した実分母二単体。 -/
def DGVerdierClosedVertexRefinement.edgeCone : (dgVerdierOver A D P x : SSet) _⦋2⦌ :=
  dgVerdierTwoSimplexInitialRefinement A D P x H.simplex R.q
    (dgClosedTargetTransport A D R.s (dgVerdierEdgeConeTetrahedron_source A D C e H).symm)
    (dgClosedTargetTransport_mem A D P R.s
      (dgVerdierEdgeConeTetrahedron_source A D C e H).symm R.denominator)

/-- 細分した辺錐の零面は、元の指定実図式辺そのもの。 -/
lemma DGVerdierClosedVertexRefinement.edgeCone_face0 :
    (dgVerdierOver A D P x : SSet).δ 0
      (DGVerdierClosedVertexRefinement.edgeCone A D R e H) = f.app _ e :=
  (dgVerdierTwoSimplexInitialRefinement_face0 A D P x H.simplex R.q
    (dgClosedTargetTransport A D R.s (dgVerdierEdgeConeTetrahedron_source A D C e H).symm)
    (dgClosedTargetTransport_mem A D P R.s
      (dgVerdierEdgeConeTetrahedron_source A D C e H).symm R.denominator)).trans H.d₀

/-- 細分した辺錐の各脚面は、その図式頂点ごとに固定した同じ単一実脚。 -/
lemma DGVerdierClosedVertexRefinement.edgeCone_face_positive (i : Fin 2) :
    (dgVerdierOver A D P x : SSet).δ i.succ (DGVerdierClosedVertexRefinement.edgeCone A D R e H) =
      ((DGVerdierClosedVertexRefinement.vertexCone A D R).leg (K.δ i e)).edge := by
  apply Subtype.ext
  apply roofPointSliceTriangle_injective
    ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))
  let sH := dgClosedTargetTransport A D R.s
    (dgVerdierEdgeConeTetrahedron_source A D C e H).symm
  change roofPointSliceTriangle _ ((sliceOver _).δ i.succ
    (dgOverTwoSimplexInitialRefinement A D x H.simplex.val R.q sH)) =
      roofPointSliceTriangle _ (DGVerdierClosedVertexRefinement.vertexLegSimplex A D R (K.δ i e))
  rw [DGVerdierClosedVertexRefinement.vertexLegSimplex_triangle A D R (K.δ i e)]
  have hf := dgOverTwoSimplexInitialRefinement_face_positive A D x H.simplex.val R.q sH i
  have hc := dgSimplexInitialRefinement_congr
    (dgVerdierEdgeConePositiveFace_triangle A D C e H i) R.q R.q
    (dgClosedTargetTransport A D sH (dgOverTwoSimplexPositiveFace_source A D x H.simplex.val i))
    (dgClosedTargetTransport A D R.s (dgVerdierDiagramLegTriangle_source A D C (K.δ i e)).symm)
    ((dgClosedTargetTransport_edge A D sH _).trans
      ((dgClosedTargetTransport_edge A D R.s _).trans
        (dgClosedTargetTransport_edge A D R.s _).symm))
  have ht := dgSimplexInitialRefinement_triangle A D (dgVerdierDiagramLegTriangle A D C (K.δ i e))
    R.q (dgClosedTargetTransport A D R.s
      (dgVerdierDiagramLegTriangle_source A D C (K.δ i e)).symm)
  exact hf.trans (congrArg (SSet.yonedaEquiv (X := dgNerve A D)).symm (hc.trans ht))

/-- 元の任意の辺錐から、同じ共通頂点錐の二脚の合成整合性を構成する。 -/
def DGVerdierClosedVertexRefinement.edgeCompStruct :
    Truncated.Edge.CompStruct ((DGVerdierClosedVertexRefinement.vertexCone A D R).leg (K.δ 1 e))
      ((edgeOfSimplex e).map ((truncation 2).map f))
      ((DGVerdierClosedVertexRefinement.vertexCone A D R).leg (K.δ 0 e)) where
  simplex := DGVerdierClosedVertexRefinement.edgeCone A D R e H
  d₂ := DGVerdierClosedVertexRefinement.edgeCone_face_positive A D R e H 1
  d₀ := DGVerdierClosedVertexRefinement.edgeCone_face0 A D R e H
  d₁ := DGVerdierClosedVertexRefinement.edgeCone_face_positive A D R e H 0

end SerrePositivity.InfinityCategories
