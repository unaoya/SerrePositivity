module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierFiniteTriangleConeFaces
public import SerrePositivity.InfinityCategories.Derived.DGVerdierClosedEdgeCones

/-! # 有限二単体族の共通閉細分頂点錐と全三単体境界

概要：同じ追加閉分母で全頂点脚・辺錐を固定し、全実三単体の錐面をその辺錐へ同定する。
方針：有限族の追加閉実辺の一致を使い、同じ元の辺錐の細分の合同性を適用する。
規約：恒等・退化整合性は別工程。使われ方：有限二次図式の共通始錐の境界組み立て。
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
variable [Small.{u} D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}
variable (C : DGVerdierDiagramVertexCone A D P x f) {m : ℕ}
variable (τ : Fin m → K _⦋2⦌)
variable (G : ∀ j, ∀ i : Fin 3, Truncated.Edge.CompStruct
  (C.leg (K.δ 1 (K.δ i (τ j))))
  ((edgeOfSimplex (K.δ i (τ j))).map ((truncation 2).map f))
  (C.leg (K.δ 0 (K.δ i (τ j)))))

variable [IsDGPretriangulated A D]
variable (T : DGVerdierFiniteTriangleRefinement A D C τ G)



/-- 有限二単体族の同じ追加閉分母を、辺族から独立な頂点細分データへ渡す。 -/
def DGVerdierFiniteTriangleRefinement.vertexRefinement :
    DGVerdierClosedVertexRefinement A D C :=
  ⟨T.q, T.s, T.denominator⟩

/-- 各実三単体の錐面は、同じ共通新頂点脚を持つ指定辺錐の合成二単体。 -/
lemma DGVerdierFiniteTriangleRefinement.simplex_face_refinedCone (j : Fin m) (i : Fin 3) :
    (dgVerdierOver A D P x : SSet).δ i.succ
      (DGVerdierFiniteTriangleRefinement.simplex A D C τ G T j) =
      (DGVerdierClosedVertexRefinement.edgeCompStruct A D
        (DGVerdierFiniteTriangleRefinement.vertexRefinement A D C τ G T)
        (K.δ i (τ j)) (G j i)).simplex := by
  rw [DGVerdierFiniteTriangleRefinement.simplex_face_cone]
  change dgVerdierDiagramRefinedEdgeCone A D C (τ j) (G j)
    (T.residuals j).q (T.residuals j).s (T.residuals j).denominator i =
      DGVerdierClosedVertexRefinement.edgeCone A D
        (DGVerdierFiniteTriangleRefinement.vertexRefinement A D C τ G T)
        (K.δ i (τ j)) (G j i)
  unfold dgVerdierDiagramRefinedEdgeCone DGVerdierClosedVertexRefinement.edgeCone
  apply dgVerdierTwoSimplexInitialRefinement_congr A D P x rfl
  exact (dgClosedTargetTransport_edge A D (T.residuals j).s _).trans
    ((T.denominator_edge_eq j).trans (dgClosedTargetTransport_edge A D T.s _).symm)

/-- 同じ頂点錐の指定実二単体有限族は、一つの閉細分頂点錐と全三単体境界を持つ。 -/
theorem dgVerdierTriangles_exists_closedRefinedVertexCone :
    ∃ (R : DGVerdierClosedVertexRefinement A D C)
      (U : Fin m → (dgVerdierOver A D P x : SSet) _⦋3⦌),
      ∀ j, (dgVerdierOver A D P x : SSet).δ 0 (U j) = f.app _ (τ j) ∧
        ∀ i : Fin 3, (dgVerdierOver A D P x : SSet).δ i.succ (U j) =
          (DGVerdierClosedVertexRefinement.edgeCompStruct A D R (K.δ i (τ j)) (G j i)).simplex := by
  obtain ⟨T⟩ := dgVerdierFiniteTriangleRefinement_nonempty A D C τ G
  exact ⟨DGVerdierFiniteTriangleRefinement.vertexRefinement A D C τ G T,
    DGVerdierFiniteTriangleRefinement.simplex A D C τ G T, fun j =>
      ⟨DGVerdierFiniteTriangleRefinement.simplex_face0 A D C τ G T j,
        DGVerdierFiniteTriangleRefinement.simplex_face_refinedCone A D C τ G T j⟩⟩

end SerrePositivity.InfinityCategories
