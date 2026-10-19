module
public import SerrePositivity.InfinityCategories.Derived.DGTriangleRefinementComponents
public import SerrePositivity.InfinityCategories.Derived.DGTriangleFaceNormalForms
public import SerrePositivity.InfinityCategories.Derived.DGClosedVerdierComposition

/-! # 実始点細分三角形の対角辺の閉合成表示

概要：細分した対角辺を元の対角閉射と追加閉射の合成と同定し、実分母性を保つ。
方針：閉 cycle の前合成と閉零圏の合成の一致を使い、実一次単体で照合する。
規約：同じ三角形の対角辺 02 を保つ。使われ方：細分した over 始頂点の実分母性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 閉 cycle の前合成は、元の閉零圏での同じ二射の合成の cycle。 -/
lemma dgClosedCyclePrecompose_comp {q x y : D} (c : zeroCycles (homObject A D x y))
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    closedHomEquiv A D _ _ (s ≫ (closedHomEquiv A D _ _).symm c) =
      dgClosedCyclePrecompose c s := by
  apply Subtype.ext
  have hc : (closedHomEquiv A D _ _ ((closedHomEquiv A D _ _).symm c)).val = c.val :=
    congrArg Subtype.val ((closedHomEquiv A D _ _).apply_symm_apply c)
  exact (closedHom_comp s ((closedHomEquiv A D _ _).symm c)).trans
    (congrArg (fun a : GradedHom A x y 0 =>
      compose A a (closedHomEquiv A D _ _ s).val (by decide)) hc)

/-- 同じ cycle による標準一次単体と、その元の閉射の実辺は厳密に同じ。 -/
lemma dgClosedCycle_symm_edge {x y : D} (c : zeroCycles (homObject A D x y)) :
    Simplex.ofEdge (pairObj x y) c =
      (dgClosedEdge A D ((closedHomEquiv A D _ _).symm c)).edge := by
  change Simplex.ofEdge (pairObj x y) c =
    Simplex.ofEdge (pairObj x y) (closedHomEquiv A D _ _ ((closedHomEquiv A D _ _).symm c))
  rw [Equiv.apply_symm_apply]

/-- 閉前合成の標準実辺は、同じ元の閉射の合成の実辺そのもの。 -/
lemma dgClosedCyclePrecompose_edge {q x y : D} (c : zeroCycles (homObject A D x y))
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    Simplex.ofEdge (pairObj q y) (dgClosedCyclePrecompose c s) =
      (dgClosedEdge A D (s ≫ (closedHomEquiv A D _ _).symm c)).edge :=
  congrArg (Simplex.ofEdge (pairObj q y)) (dgClosedCyclePrecompose_comp A D c s).symm

/-- 実三角形の元の対角閉射。 -/
def dgSimplexClosedDiagonal (t : Simplex A D 2) :
    ForgetEnrichment.of (Complex A) (t.obj 0) ⟶ ForgetEnrichment.of (Complex A) (t.obj 2) :=
  (closedHomEquiv A D _ _).symm (t.edgeCycle 0 2 (by decide))

/-- 元の対角閉射の実辺は、その実三角形の指定一面そのもの。 -/
lemma dgSimplexClosedDiagonal_edge (t : Simplex A D 2) :
    (dgNerve A D).δ 1 t = (dgClosedEdge A D (dgSimplexClosedDiagonal A D t)).edge :=
  (dgTriangleFace1_normal t).trans (dgClosedCycle_symm_edge A D _)

/-- 実始点細分した対角辺は、追加閉射と元の対角閉射の実合成。 -/
lemma dgSimplexSourceRefinement_face1_comp (t : Simplex A D 2) (q : D)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) (t.obj 0)) :
    (dgNerve A D).δ 1 (dgSimplexSourceRefinement t q s) =
      (dgClosedEdge A D (s ≫ dgSimplexClosedDiagonal A D t)).edge :=
  (dgSimplexSourceRefinement_face1 t q s).trans (dgClosedCyclePrecompose_edge A D _ s)

variable [Small.{u} D] [IsDGPretriangulated A D]

/-- 元の対角辺と追加閉射が実分母なら、同じ実細分対角辺も実分母。 -/
lemma dgSimplexSourceRefinement_face1_mem (P : Set D) (t : Simplex A D 2) (q : D)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) (t.obj 0))
    (ht : (dgNerve A D).δ 1 t ∈ dgVerdierEdges A D P)
    (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P) :
    (dgNerve A D).δ 1 (dgSimplexSourceRefinement t q s) ∈ dgVerdierEdges A D P := by
  rw [dgSimplexSourceRefinement_face1_comp]
  exact dgClosedVerdierDenominator_comp A D P s (dgSimplexClosedDiagonal A D t) hs
    ((congrArg (fun e => e ∈ dgVerdierEdges A D P) (dgSimplexClosedDiagonal_edge A D t)).mp ht)

end SerrePositivity.InfinityCategories
