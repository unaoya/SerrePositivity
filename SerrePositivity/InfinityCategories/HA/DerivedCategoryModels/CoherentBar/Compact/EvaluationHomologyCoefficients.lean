module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.EvaluationCoconeGeometry
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeHomologyColimit
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoconeHomologyLegs
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyEdges
/-!
概要：実評価チャートの係数を、同じ native bar のホモロジー余錐へ合わせる。
方針：元の辺と脚を回収し、既存の H⁰ 比較の自然同型を使う。
規約：元の全次数と同じ余錐の全ての脚を保持する。
使われ方：評価ホモロジー余極限から空間の五条件を導く。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial

lemma dgBarCompactModuleEdgeClosed_heq (R : Type u) [CommRing R]
    (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
    {y z y' z' : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) _⦋0⦌}
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)).Edge y z)
    (e' : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)).Edge y' z') (h : e.edge = e'.edge) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e.toTruncated) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e'.toTruncated) := by
  have hy : y = y' := e.src_eq.symm.trans
    ((congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)).δ 1) h).trans e'.src_eq)
  have hz : z = z' := e.tgt_eq.symm.trans
    ((congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)).δ 0) h).trans e'.tgt_eq)
  subst y'; subst z'
  have he : e = e' := SSet.Edge.ext h
  subst e'
  rfl

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : Type u} [PartialOrder I]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve I) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleNerve R D)
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G) (x : D)

/-- 既存 H⁰ 図式の対象と、同じ実評価複体のコホモロジー。 -/
def dgBarCompactEvaluationStageHomologyIso (q : ℤ) (i : I) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarDiagram R D G) x q).obj i ≅
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationStageVertex R D G i) :
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D).val.obj (Opposite.op x)).homology q) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagramObjIso R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarDiagram R D G) x q i

lemma dgBarCompactEvaluationTransitionClosed_eq {i j : I} (h : i ≤ j) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationIndexEdge R D G h).toTruncated.map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D))))) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarDiagramEdge R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarDiagram R D G) (homOfLE h) := rfl

lemma dgBarCompactEvaluationLegClosed_eq (i : I) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationLegEdge R D G c i).toTruncated.map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D))))) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationHomotopy
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullInclusionCocone R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)
            c))
        (ULift.up (nerveEquiv.symm i))).toTruncated := by
  let E := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D))
  let e₁ := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationLegEdge R D G c i).map E
  let e₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone E c)) (ULift.up (nerveEquiv.symm i))
  have hraw : e₁.edge = e₂.edge := by
    change E.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationLegEdge R D G c i).edge = e₂.edge
    have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeHomotopyLeg_edge c (ULift.up (nerveEquiv.symm i))
    have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeHomotopyLeg_edge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone E c) (ULift.up (nerveEquiv.symm i))
    change E.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationHomotopy c)
        (ULift.up (nerveEquiv.symm i))).edge = e₂.edge
    rw [h₁, ← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactCoconeLeg_map]
    exact h₂.symm
  exact eq_of_heq (dgBarCompactModuleEdgeClosed_heq R D e₁ e₂ hraw)

lemma dgBarCompactEvaluationStageHomologyIso_inv_naturality
    (q : ℤ) {i j : I} (f : i ⟶ j) :
    HomologicalComplex.homologyMap ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarDiagramEdge R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarDiagram R D G) f)) q ≫
        (dgBarCompactEvaluationStageHomologyIso R D G x q j).inv =
      (dgBarCompactEvaluationStageHomologyIso R D G x q i).inv ≫
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarDiagram R D G) x q).map f := by
  dsimp only [dgBarCompactEvaluationStageHomologyIso]
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagramObjIso R D
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarDiagram R D G) x q j).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagramObjIso_naturality]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

lemma dgBarCompactEvaluationHomologyLeg (q : ℤ) (i : I) :
    (dgBarCompactEvaluationStageHomologyIso R D G x q i).inv ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentCoconeHomology R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgProjectiveBarDiagram R D G)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullInclusionCocone R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)
          c) x q).ι.app i =
      HomologicalComplex.homologyMap ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactEvaluationLegEdge R D G c i).toTruncated.map
          ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D))))))) q := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentCoconeHomology_leg, dgBarCompactEvaluationLegClosed_eq]
  simp only [dgBarCompactEvaluationStageHomologyIso, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
