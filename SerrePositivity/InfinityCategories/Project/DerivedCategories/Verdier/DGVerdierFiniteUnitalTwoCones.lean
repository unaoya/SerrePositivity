module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierFiniteTriangleVertexCone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierNormalizedEdgeCones
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierFiniteLegCompatibility

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 有限二次実図式には、退化辺で標準単位錐を選ぶ同じ頂点錐と全四面整合性がある。 -/
theorem dgVerdierDiagramFiniteTriangles_exists_unitalVertexCone
    (P : Set D) (x : D) {K : SSet.{max u v}} [Finite (K _⦋0⦌)] [Finite (K _⦋1⦌)]
    (f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})) {m : ℕ} (τ : Fin m → K _⦋2⦌) :
    ∃ (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f)
      (H : ∀ e : K _⦋1⦌, Truncated.Edge.CompStruct
        (C.leg (K.δ 1 e)) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)))
      (U : Fin m → (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋3⦌),
      (∀ v : K _⦋0⦌, (H (K.σ 0 v)).simplex =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).σ 1 (C.leg v).edge) ∧
      ∀ j, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0 (U j) = f.app _ (τ j) ∧
        ∀ i : Fin 3, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ i.succ (U j) = (H (K.δ i (τ j))).simplex := by
  classical
  let : Fintype (K _⦋1⦌) := Fintype.ofFinite _
  let ε := Fintype.equivFin (K _⦋1⦌)
  obtain ⟨C, hC⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramFiniteEdges_exists_vertexCone A D P x f (fun i => ε.symm i)
  let E (i : Fin (Fintype.card (K _⦋1⦌))) := Classical.choice (hC i)
  have G (e : K _⦋1⦌) : Truncated.Edge.CompStruct
      (C.leg (K.δ 1 e)) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)) := by
    have h := E (ε e)
    rw [ε.symm_apply_apply] at h
    exact h
  obtain ⟨R, U, hU⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierTriangles_exists_closedRefinedVertexCone A D C τ
    (fun j i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramNormalizeEdgeCone A D C G (K.δ i (τ j)))
  exact ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.vertexCone A D R,
    (fun e => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.edgeCompStruct A D R e
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramNormalizeEdgeCone A D C G e)), U,
    (fun v => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.normalizedIdentityEdgeCone_simplex A D G R v), hU⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
