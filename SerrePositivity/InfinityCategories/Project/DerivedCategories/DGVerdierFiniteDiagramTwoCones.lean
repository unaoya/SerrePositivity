module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteTriangleVertexCone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteLegCompatibility

/-! # 有限二次図式の一つの頂点錐と全指定二単体の実三次整合性

概要：有限頂点・辺の図式へ単一頂点錐・全辺錐・指定有限二単体の全四面整合性を供給。
方針：全辺を有限番号へ移して同じ元の辺錐を固定し、一つの追加閉細分を同時適用する。
規約：恒等・退化との可換性を含む全単体的錐は別工程。使われ方：実有限共通錐の二次段階。
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

/-- 有限頂点・辺の実図式の任意の有限二単体族は、同じ頂点錐の全辺錐と三次整合性を持つ。 -/
theorem dgVerdierDiagramFiniteTriangles_exists_vertexCone
    (P : Set D) (x : D) {K : SSet.{max u v}} [Finite (K _⦋0⦌)] [Finite (K _⦋1⦌)]
    (f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})) {m : ℕ} (τ : Fin m → K _⦋2⦌) :
    ∃ (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f)
      (H : ∀ e : K _⦋1⦌, Truncated.Edge.CompStruct
        (C.leg (K.δ 1 e)) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)))
      (U : Fin m → (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋3⦌),
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
    (fun j i => G (K.δ i (τ j)))
  exact ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.vertexCone A D R,
    (fun e => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.edgeCompStruct A D R e (G e)), U, hU⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
