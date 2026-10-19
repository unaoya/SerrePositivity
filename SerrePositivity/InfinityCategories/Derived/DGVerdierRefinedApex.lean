module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierInitialDiagonal
public import SerrePositivity.InfinityCategories.Derived.RoofTetrahedronApexEdge
public import SerrePositivity.InfinityCategories.Derived.DGVerdierRefinedDiagramTriangle

/-! # 細分した実図式三角形の新始頂点の実分母性

概要：回収 over 三角形の新始頂点の指定辺は、同じ閉細分した対角分母辺である。
方針：四面体からの始頂点辺公式と、元の対角分母の閉合成表示を接続する。
規約：追加閉分母と元の指定集合を保つ。使われ方：実分母全部分複体への三角形持ち上げ。
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
variable (C : DGVerdierDiagramVertexCone A D P x f) (e : K _⦋1⦌)

/-- 回収 over 三角形の新始頂点の辺は、同じ実細分面 023 の対角辺 03。 -/
lemma dgVerdierDiagramRefinedApex_edge (q : D)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
      ((HornData.knownData (dgVerdierDiagramEdgeHorn A D C e)).obj 0))
    (F : Δ[3] ⟶ dgNerve A D)
    (hF : (horn 3 3).ι ≫ F = dgLastHornSourceRefinement (dgVerdierDiagramEdgeHorn A D C e) q s) :
    (roofPointSliceVertexEdge _
      ((sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))).δ 1
        ((sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))).δ 1
          (dgVerdierDiagramRefinedOverTriangle A D C e q s F hF)))).edge =
      (dgNerve A D).δ 1 (dgLastHornRefinedFace1 (dgVerdierDiagramEdgeHorn A D C e) q s) := by
  have h₁ : SSet.stdSimplex.δ (1 : Fin 4) ≫ F =
      (SSet.yonedaEquiv (X := dgNerve A D)).symm
        (dgLastHornRefinedFace1 (dgVerdierDiagramEdgeHorn A D C e) q s) := by
    rw [← horn.ι_ι_assoc (3 : Fin 4) 1 (by decide), hF, dgLastHornSourceRefinement_face1]
  have hA := roofPointSliceTwoSimplexOfTetrahedron_apex_edge _
    (((edgeOfSimplex e).map ((truncation 2).map f)).map
      ((truncation 2).map (dgVerdierOver A D P x).ι)) F
    (dgVerdierDiagramRefinedFiller_face0 A D C e q s F hF)
  exact hA.trans ((congrArg (fun g => (dgNerve A D).δ 1
    ((SSet.yonedaEquiv (X := dgNerve A D)) g)) h₁).trans
      (congrArg ((dgNerve A D).δ (1 : Fin 3))
        ((SSet.yonedaEquiv (X := dgNerve A D)).apply_symm_apply _)))

variable [Small.{u} D] [IsDGPretriangulated A D]

/-- 元の追加閉分母後の実 over 三角形の新始頂点も、同じ実 Verdier 分母条件を満たす。 -/
lemma dgVerdierDiagramRefinedApex_mem (q : D)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
      ((HornData.knownData (dgVerdierDiagramEdgeHorn A D C e)).obj 0))
    (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P)
    (F : Δ[3] ⟶ dgNerve A D)
    (hF : (horn 3 3).ι ≫ F = dgLastHornSourceRefinement (dgVerdierDiagramEdgeHorn A D C e) q s) :
    IsDGVerdierOverVertex A D P x
      ((sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))).δ 1
        ((sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))).δ 1
          (dgVerdierDiagramRefinedOverTriangle A D C e q s F hF))) := by
  unfold IsDGVerdierOverVertex
  rw [dgVerdierDiagramRefinedApex_edge]
  exact dgSimplexSourceRefinement_face1_mem A D P
    (dgLastHornCanonicalFace (dgVerdierDiagramEdgeHorn A D C e) 1 (by decide)) q s
    (dgVerdierDiagramInitialDiagonal_mem A D P x C e) hs

end SerrePositivity.InfinityCategories
