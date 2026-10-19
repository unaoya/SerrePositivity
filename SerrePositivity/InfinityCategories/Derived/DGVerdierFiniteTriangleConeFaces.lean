module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierFiniteTriangleCommonApex
public import SerrePositivity.InfinityCategories.Derived.DGVerdierRefinedThreeConeFaces
public import SerrePositivity.InfinityCategories.Derived.DGVerdierTwoSimplexRefinementCongruence

/-! # 有限同時細分の実三単体の共通錐面

概要：各三単体の正番号面を指定辺錐の細分へ戻し、同じ元の辺錐なら新面も厳密に一致。
方針：追加閉分母の実辺の共通性と、実分母二単体の細分の合同性を接続する。
規約：元の辺錐の一致を入力として明示。使われ方：有限二次図式の境界整合性。
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


/-- 有限族の各実三単体の正番号面は、元の指定辺錐の同じ閉始点細分。 -/
lemma DGVerdierFiniteTriangleRefinement.simplex_face_cone (j : Fin m) (i : Fin 3) :
    (dgVerdierOver A D P x : SSet).δ i.succ
      (DGVerdierFiniteTriangleRefinement.simplex A D C τ G T j) =
      dgVerdierDiagramRefinedEdgeCone A D C (τ j) (G j)
        (T.residuals j).q (T.residuals j).s (T.residuals j).denominator i :=
  dgVerdierDiagramRefinedThreeSimplex_face_cone A D C (τ j) (G j)
    (T.residuals j).q (T.residuals j).s (T.residuals j).denominator
    (T.filler j) (T.filler_fac j) i

/-- 元の辺錐が同じ二つの面は、同じ追加実閉分母後にも厳密に同じ面となる。 -/
lemma DGVerdierFiniteTriangleRefinement.commonConeFace_eq
    (j j' : Fin m) (i i' : Fin 3) (h : (G j i).simplex = (G j' i').simplex) :
    (dgVerdierOver A D P x : SSet).δ i.succ
      (DGVerdierFiniteTriangleRefinement.simplex A D C τ G T j) =
      (dgVerdierOver A D P x : SSet).δ i'.succ
        (DGVerdierFiniteTriangleRefinement.simplex A D C τ G T j') := by
  rw [DGVerdierFiniteTriangleRefinement.simplex_face_cone,
    DGVerdierFiniteTriangleRefinement.simplex_face_cone]
  unfold dgVerdierDiagramRefinedEdgeCone
  apply dgVerdierTwoSimplexInitialRefinement_congr A D P x h
  exact (dgClosedTargetTransport_edge A D (T.residuals j).s _).trans
    ((T.denominator_edge_eq j).trans ((T.denominator_edge_eq j').symm.trans
      (dgClosedTargetTransport_edge A D (T.residuals j').s _).symm))

end SerrePositivity.InfinityCategories
