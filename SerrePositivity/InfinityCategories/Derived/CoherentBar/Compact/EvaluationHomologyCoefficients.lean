module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationCoconeGeometry
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeHomologyColimit
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoconeHomologyLegs
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyEdges
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial

lemma dgBarCompactModuleEdgeClosed_heq (R : Type u) [CommRing R]
    (D : Type v) [DGCategory R D] [Small.{u} D]
    {y z y' z' : (dgNerve R (RightModule R D)) _⦋0⦌}
    (e : (dgNerve R (RightModule R D)).Edge y z)
    (e' : (dgNerve R (RightModule R D)).Edge y' z') (h : e.edge = e'.edge) :
    HEq (edgeClosed e.toTruncated) (edgeClosed e'.toTruncated) := by
  have hy : y = y' := e.src_eq.symm.trans
    ((congrArg ((dgNerve R (RightModule R D)).δ 1) h).trans e'.src_eq)
  have hz : z = z' := e.tgt_eq.symm.trans
    ((congrArg ((dgNerve R (RightModule R D)).δ 0) h).trans e'.tgt_eq)
  subst y'; subst z'
  have he : e = e' := SSet.Edge.ext h
  subst e'
  rfl

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : Type u} [PartialOrder I]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve I) ⟶ dgProjectiveModuleNerve R D)
  (c : JoinCocone G) (x : D)

/-- 既存 H⁰ 図式の対象と、同じ実評価複体のコホモロジー。 -/
def dgBarCompactEvaluationStageHomologyIso (q : ℤ) (i : I) :
    (dgCoherentBarHomologyDiagram R D (dgProjectiveBarDiagram R D G) x q).obj i ≅
      (((Simplex.vertexEquiv (dgBarCompactEvaluationStageVertex R D G i) :
        ProjectiveDGModules R D).val.obj (Opposite.op x)).homology q) :=
  dgCoherentBarHomologyDiagramObjIso R D (dgProjectiveBarDiagram R D G) x q i

lemma dgBarCompactEvaluationTransitionClosed_eq {i j : I} (h : i ≤ j) :
    edgeClosed ((dgBarCompactEvaluationIndexEdge R D G h).toTruncated.map
      ((truncation 2).map (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
        (dgModuleProjectiveProperty R D))))) =
      dgCoherentBarDiagramEdge R D (dgProjectiveBarDiagram R D G) (homOfLE h) := rfl

lemma dgBarCompactEvaluationLegClosed_eq (i : I) :
    edgeClosed ((dgBarCompactEvaluationLegEdge R D G c i).toTruncated.map
      ((truncation 2).map (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
        (dgModuleProjectiveProperty R D))))) =
      edgeClosed (simplicialHomotopyVertexEdge
        (F2.coconeTransformationHomotopy
          (fullInclusionCocone R (RightModule R D) (dgModuleProjectiveProperty R D)
            c))
        (ULift.up (nerveEquiv.symm i))).toTruncated := by
  let E := dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D))
  let e₁ := (dgBarCompactEvaluationLegEdge R D G c i).map E
  let e₂ := simplicialHomotopyVertexEdge
    (F2.coconeTransformationHomotopy (mapJoinCocone E c)) (ULift.up (nerveEquiv.symm i))
  have hraw : e₁.edge = e₂.edge := by
    change E.app (Opposite.op ⦋1⦌) (dgBarCompactEvaluationLegEdge R D G c i).edge = e₂.edge
    have h₁ := F2.Compact.coconeHomotopyLeg_edge c (ULift.up (nerveEquiv.symm i))
    have h₂ := F2.Compact.coconeHomotopyLeg_edge (mapJoinCocone E c) (ULift.up (nerveEquiv.symm i))
    change E.app (Opposite.op ⦋1⦌)
      (simplicialHomotopyVertexEdge (F2.coconeTransformationHomotopy c)
        (ULift.up (nerveEquiv.symm i))).edge = e₂.edge
    rw [h₁, ← dgBarCompactCoconeLeg_map]
    exact h₂.symm
  exact eq_of_heq (dgBarCompactModuleEdgeClosed_heq R D e₁ e₂ hraw)

lemma dgBarCompactEvaluationStageHomologyIso_inv_naturality
    (q : ℤ) {i j : I} (f : i ⟶ j) :
    HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
      (dgCoherentBarDiagramEdge R D (dgProjectiveBarDiagram R D G) f)) q ≫
        (dgBarCompactEvaluationStageHomologyIso R D G x q j).inv =
      (dgBarCompactEvaluationStageHomologyIso R D G x q i).inv ≫
        (dgCoherentBarHomologyDiagram R D (dgProjectiveBarDiagram R D G) x q).map f := by
  dsimp only [dgBarCompactEvaluationStageHomologyIso]
  apply (cancel_mono (dgCoherentBarHomologyDiagramObjIso R D
    (dgProjectiveBarDiagram R D G) x q j).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [dgCoherentBarHomologyDiagramObjIso_naturality]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

lemma dgBarCompactEvaluationHomologyLeg (q : ℤ) (i : I) :
    (dgBarCompactEvaluationStageHomologyIso R D G x q i).inv ≫
      (dgCoherentCoconeHomology R D (dgProjectiveBarDiagram R D G)
        (fullInclusionCocone R (RightModule R D) (dgModuleProjectiveProperty R D)
          c) x q).ι.app i =
      HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
        (edgeClosed ((dgBarCompactEvaluationLegEdge R D G c i).toTruncated.map
          ((truncation 2).map (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
            (dgModuleProjectiveProperty R D))))))) q := by
  rw [dgCoherentCoconeHomology_leg, dgBarCompactEvaluationLegClosed_eq]
  simp only [dgBarCompactEvaluationStageHomologyIso, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end SerrePositivity.InfinityCategories
