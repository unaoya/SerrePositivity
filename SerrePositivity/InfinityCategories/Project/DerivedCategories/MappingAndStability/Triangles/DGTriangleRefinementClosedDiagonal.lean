module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGTriangleRefinementComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGTriangleFaceNormalForms
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGClosedVerdierComposition

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 閉 cycle の前合成は、元の閉零圏での同じ二射の合成の cycle。 -/
lemma dgClosedCyclePrecompose_comp {q x y : D} (c : _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.homObject A D x y))
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    _root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ (s ≫ (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _).symm c) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedCyclePrecompose c s := by
  apply Subtype.ext
  have hc : (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _).symm c)).val = c.val :=
    congrArg Subtype.val ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _).apply_symm_apply c)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_comp s ((closedHomEquiv A D _ _).symm c)).trans
    (congrArg (fun a : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y 0 =>
      _root_.SerrePositivity.DifferentialGraded.compose A a (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val (by decide)) hc)

/-- 同じ cycle による標準一次単体と、その元の閉射の実辺は厳密に同じ。 -/
lemma dgClosedCycle_symm_edge {x y : D} (c : _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.homObject A D x y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj x y) c =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D ((closedHomEquiv A D _ _).symm c)).edge := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj x y) c =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj x y) (closedHomEquiv A D _ _ ((closedHomEquiv A D _ _).symm c))
  rw [Equiv.apply_symm_apply]

/-- 閉前合成の標準実辺は、同じ元の閉射の合成の実辺そのもの。 -/
lemma dgClosedCyclePrecompose_edge {q x y : D} (c : _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.homObject A D x y))
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj q y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedCyclePrecompose c s) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (s ≫ (closedHomEquiv A D _ _).symm c)).edge :=
  congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj q y)) (dgClosedCyclePrecompose_comp A D c s).symm

/-- 実三角形の元の対角閉射。 -/
def dgSimplexClosedDiagonal (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2) :
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (t.obj 0) ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (t.obj 2) :=
  (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _).symm (t.edgeCycle 0 2 (by decide))

/-- 元の対角閉射の実辺は、その実三角形の指定一面そのもの。 -/
lemma dgSimplexClosedDiagonal_edge (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 t = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (dgSimplexClosedDiagonal A D t)).edge :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTriangleFace1_normal t).trans (dgClosedCycle_symm_edge A D _)

/-- 実始点細分した対角辺は、追加閉射と元の対角閉射の実合成。 -/
lemma dgSimplexSourceRefinement_face1_comp (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2) (q : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (t.obj 0)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexSourceRefinement t q s) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (s ≫ dgSimplexClosedDiagonal A D t)).edge :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexSourceRefinement_face1 t q s).trans (dgClosedCyclePrecompose_edge A D _ s)

variable [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 元の対角辺と追加閉射が実分母なら、同じ実細分対角辺も実分母。 -/
lemma dgSimplexSourceRefinement_face1_mem (P : Set D) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2) (q : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (t.obj 0))
    (ht : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 t ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexSourceRefinement t q s) ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P := by
  rw [dgSimplexSourceRefinement_face1_comp]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominator_comp A D P s (dgSimplexClosedDiagonal A D t) hs
    ((congrArg (fun e => e ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) (dgSimplexClosedDiagonal_edge A D t)).mp ht)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
