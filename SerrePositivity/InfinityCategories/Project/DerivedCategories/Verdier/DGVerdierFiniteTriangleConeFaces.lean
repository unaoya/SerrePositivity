module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierFiniteTriangleCommonApex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierRefinedThreeConeFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierTwoSimplexRefinementCongruence

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


/-- 有限族の各実三単体の正番号面は、元の指定辺錐の同じ閉始点細分。 -/
lemma DGVerdierFiniteTriangleRefinement.simplex_face_cone (j : Fin m) (i : Fin 3) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ i.succ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteTriangleRefinement.simplex A D C τ G T j) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedEdgeCone A D C (τ j) (G j)
        (T.residuals j).q (T.residuals j).s (T.residuals j).denominator i :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedThreeSimplex_face_cone A D C (τ j) (G j)
    (T.residuals j).q (T.residuals j).s (T.residuals j).denominator
    (T.filler j) (T.filler_fac j) i

/-- 元の辺錐が同じ二つの面は、同じ追加実閉分母後にも厳密に同じ面となる。 -/
lemma DGVerdierFiniteTriangleRefinement.commonConeFace_eq
    (j j' : Fin m) (i i' : Fin 3) (h : (G j i).simplex = (G j' i').simplex) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ i.succ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteTriangleRefinement.simplex A D C τ G T j) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ i'.succ
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteTriangleRefinement.simplex A D C τ G T j') := by
  rw [DGVerdierFiniteTriangleRefinement.simplex_face_cone,
    DGVerdierFiniteTriangleRefinement.simplex_face_cone]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedEdgeCone
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierTwoSimplexInitialRefinement_congr A D P x h
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D (T.residuals j).s _).trans
    ((T.denominator_edge_eq j).trans ((T.denominator_edge_eq j').symm.trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D (T.residuals j').s _).symm))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
