module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInitialRefinementPositiveFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGTriangleRefinementClosedDiagonal

/-! # 任意次元の閉始点細分の一次元表示と四面体の始点対角辺

概要：実辺の閉始点細分は閉射の合成であり、四面体の始点対角辺にも同じ表示を与える。
方針：一次元では閉 cycle と対象族で比較し、四面体では二つの正番号面との可換性を使う。
規約：同じ指定閉射を保つ。使われ方：細分した over 三単体の新 apex の実分母性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 任意の実一次単体の、元の閉射による厳密な表示。 -/
lemma dgSimplexEdge_closed_normal (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 1) :
    t = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (t.edgeClosed 0 1 (by decide))).edge := by
  change t = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj (t.obj 0) (t.obj 1))
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ ((_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _).symm (t.edgeCycle 0 1 (by decide))))
  rw [Equiv.apply_symm_apply]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
  refine Sigma.ext ?_ (heq_of_eq rfl)
  funext i
  fin_cases i <;> rfl

/-- 実一次単体の一般閉始点細分は、元の閉射への同じ閉前合成。 -/
lemma dgSimplexInitialRefinement_edge_comp (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 1) (q : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (t.obj 0)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D t q s =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (s ≫ t.edgeClosed 0 1 (by decide))).edge := by
  have hc : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D t q s).edgeCycle 0 1 (by decide) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedCyclePrecompose (t.edgeCycle 0 1 (by decide)) s := by
    apply Subtype.ext
    rfl
  have hn : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D t q s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj q (t.obj 1))
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D t q s).edgeCycle 0 1 (by decide)) := by
    exact (dgSimplexEdge_closed_normal A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D t q s)).trans
      (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge _) ((closedHomEquiv A D _ _).apply_symm_apply _))
  rw [hc] at hn
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D t q s =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj q (t.obj 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedCyclePrecompose (t.edgeCycle 0 1 (by decide)) s)
      at hn
  exact hn.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedCyclePrecompose_edge A D (t.edgeCycle 0 1 (by decide)) s)

/-- 四面体の始点対角辺の細分は、同じ元の閉対角射への閉前合成。 -/
lemma dgTetrahedronInitialRefinement_initialDiagonal (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 3) (q : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (t.obj 0)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D t q s)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (s ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 t)).edgeClosed
        0 1 (by decide))).edge := by
  have h₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D t q s) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 t) q s := by
    have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_face_positive A D t q s 1 (by decide)
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport, eqToHom_refl, Category.comp_id] at h
    exact h
  have h₂ : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 t) q s) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 t)) q s := by
    have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_face_positive A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 t)
      q s 1 (by decide)
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport, eqToHom_refl, Category.comp_id] at h
    exact h
  rw [h₁, h₂]
  exact dgSimplexInitialRefinement_edge_comp A D
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 t)) q s

end SerrePositivity.InfinityCategories.Project.DerivedCategories
