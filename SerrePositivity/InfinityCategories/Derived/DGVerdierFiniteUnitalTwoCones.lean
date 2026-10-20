module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierFiniteTriangleVertexCone
public import SerrePositivity.InfinityCategories.Derived.DGVerdierNormalizedEdgeCones
public import SerrePositivity.InfinityCategories.Derived.DGVerdierFiniteLegCompatibility

/-! # 恒等整合的な全辺錐を持つ有限二次図式の同時整合性

概要：有限頂点・辺の図式に、全退化辺で標準単位錐を選ぶ同じ頂点錐と二次整合性を供給。
方針：元の全辺錐を正規化してから同時閉細分し、その標準単位の厳密保存を使う。
規約：二次以上の退化整合性は別工程。使われ方：全単体的有限共通錐の単位段階。
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

/-- 有限二次実図式には、退化辺で標準単位錐を選ぶ同じ頂点錐と全四面整合性がある。 -/
theorem dgVerdierDiagramFiniteTriangles_exists_unitalVertexCone
    (P : Set D) (x : D) {K : SSet.{max u v}} [Finite (K _⦋0⦌)] [Finite (K _⦋1⦌)]
    (f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})) {m : ℕ} (τ : Fin m → K _⦋2⦌) :
    ∃ (C : DGVerdierDiagramVertexCone A D P x f)
      (H : ∀ e : K _⦋1⦌, Truncated.Edge.CompStruct
        (C.leg (K.δ 1 e)) ((edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)))
      (U : Fin m → (dgVerdierOver A D P x : SSet) _⦋3⦌),
      (∀ v : K _⦋0⦌, (H (K.σ 0 v)).simplex =
        (dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge) ∧
      ∀ j, (dgVerdierOver A D P x : SSet).δ 0 (U j) = f.app _ (τ j) ∧
        ∀ i : Fin 3, (dgVerdierOver A D P x : SSet).δ i.succ (U j) = (H (K.δ i (τ j))).simplex := by
  classical
  let : Fintype (K _⦋1⦌) := Fintype.ofFinite _
  let ε := Fintype.equivFin (K _⦋1⦌)
  obtain ⟨C, hC⟩ := dgVerdierDiagramFiniteEdges_exists_vertexCone A D P x f (fun i => ε.symm i)
  let E (i : Fin (Fintype.card (K _⦋1⦌))) := Classical.choice (hC i)
  have G (e : K _⦋1⦌) : Truncated.Edge.CompStruct
      (C.leg (K.δ 1 e)) ((edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)) := by
    have h := E (ε e)
    rw [ε.symm_apply_apply] at h
    exact h
  obtain ⟨R, U, hU⟩ := dgVerdierTriangles_exists_closedRefinedVertexCone A D C τ
    (fun j i => dgVerdierDiagramNormalizeEdgeCone A D C G (K.δ i (τ j)))
  exact ⟨DGVerdierClosedVertexRefinement.vertexCone A D R,
    (fun e => DGVerdierClosedVertexRefinement.edgeCompStruct A D R e
      (dgVerdierDiagramNormalizeEdgeCone A D C G e)), U,
    (fun v => DGVerdierClosedVertexRefinement.normalizedIdentityEdgeCone_simplex A D G R v), hU⟩

end SerrePositivity.InfinityCategories
