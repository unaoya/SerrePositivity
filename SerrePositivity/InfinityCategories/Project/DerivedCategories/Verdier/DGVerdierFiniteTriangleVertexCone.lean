module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierFiniteTriangleConeFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierClosedEdgeCones

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable [Small.{u} D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f) {m : ℕ}
variable (τ : Fin m → K _⦋2⦌)
variable (G : ∀ j, ∀ i : Fin 3, Truncated.Edge.CompStruct
  (C.leg (K.δ 1 (K.δ i (τ j))))
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (K.δ i (τ j))).map ((truncation 2).map f))
  (C.leg (K.δ 0 (K.δ i (τ j)))))

variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (T : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteTriangleRefinement A D C τ G)



/-- 有限二単体族の同じ追加閉分母を、辺族から独立な頂点細分データへ渡す。 -/
def DGVerdierFiniteTriangleRefinement.vertexRefinement :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement A D C :=
  ⟨T.q, T.s, T.denominator⟩

/-- 各実三単体の錐面は、同じ共通新頂点脚を持つ指定辺錐の合成二単体。 -/
lemma DGVerdierFiniteTriangleRefinement.simplex_face_refinedCone (j : Fin m) (i : Fin 3) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ i.succ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteTriangleRefinement.simplex A D C τ G T j) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.edgeCompStruct A D
        (DGVerdierFiniteTriangleRefinement.vertexRefinement A D C τ G T)
        (K.δ i (τ j)) (G j i)).simplex := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteTriangleRefinement.simplex_face_cone]
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedEdgeCone A D C (τ j) (G j)
    (T.residuals j).q (T.residuals j).s (T.residuals j).denominator i =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.edgeCone A D
        (DGVerdierFiniteTriangleRefinement.vertexRefinement A D C τ G T)
        (K.δ i (τ j)) (G j i)
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedEdgeCone _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.edgeCone
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierTwoSimplexInitialRefinement_congr A D P x rfl
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D (T.residuals j).s _).trans
    ((T.denominator_edge_eq j).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D T.s _).symm)

/-- 同じ頂点錐の指定実二単体有限族は、一つの閉細分頂点錐と全三単体境界を持つ。 -/
theorem dgVerdierTriangles_exists_closedRefinedVertexCone :
    ∃ (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement A D C)
      (U : Fin m → (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋3⦌),
      ∀ j, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0 (U j) = f.app _ (τ j) ∧
        ∀ i : Fin 3, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ i.succ (U j) =
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.edgeCompStruct A D R (K.δ i (τ j)) (G j i)).simplex := by
  obtain ⟨T⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierFiniteTriangleRefinement_nonempty A D C τ G
  exact ⟨DGVerdierFiniteTriangleRefinement.vertexRefinement A D C τ G T,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteTriangleRefinement.simplex A D C τ G T, fun j =>
      ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteTriangleRefinement.simplex_face0 A D C τ G T j,
        DGVerdierFiniteTriangleRefinement.simplex_face_refinedCone A D C τ G T j⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
