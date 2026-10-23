module

public import SerrePositivity.InfinityCategories.F1.Coherent.UniversalCoherentReconstructionComponents
public import SerrePositivity.InfinityCategories.F1.Coherent.FamilyCurryEvaluation
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorIsoVertexEvaluation
public import SerrePositivity.InfinityCategories.F1.Coherent.StraighteningCounitNaturality

/-!
概要：普遍余単位の実際の頂点成分と個別に選んだ余単位の一致。
方針：同じ普遍表現を頂点で制限し底変換の自然性を評価の公式で移す。
規約：関手同型の指定された成分そのものを比較する。
使われ方：全図式にわたる余単位と個別の分類選択の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：普遍余単位の成分は普遍再構成の成分比較と選択した余単位の合成。
方針：普遍図式への制限の自然性と curry した同型の頂点評価を同時に使う。
規約：同型の存在ではなく指定された実際の成分の等式。
使われ方：普遍族の自然な比較と個別の選択を同じ余単位へ戻す。 -/
lemma universalCoherentReconstructionCounitIso_app {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) :
    (universalCoherentReconstructionCounitIso B).app (functorVertex F) =
      universalCoherentReconstructionComponentIso F ≪≫ coherentStraighteningCounit F := by
  let U := uncurry (𝟙 ((ihom B).obj SpaceInfinity.{u}))
  let g : B ⟶ B ⊗ (ihom B).obj SpaceInfinity.{u} :=
    lift (𝟙 B) (SSet.const (functorVertex F))
  have h : g ≫ U = F := by
    rw [uncurry_at_vertex]
    exact (functorVertexEquiv B SpaceInfinity).symm_apply_apply F
  let C := smallFiberLeftStraighteningDiagram (leftUnstraighteningProjection U)
    (leftUnstraighteningProjection_hasSmallSimplexFibers U)
  have hv : functorVertex (g ≫ C) =
      (universalCoherentReconstructionMap B).app _ (functorVertex F) := by
    have hv := functorVertex_uncurry_at_vertex (universalCoherentReconstructionMap B)
      (functorVertex F)
    simpa only [universalCoherentReconstructionMap, uncurry_curry, g, C, U] using hv
  have hc : universalCoherentReconstructionComponentIso F =
      (eqToIso (congrArg SSet.HomotopyCategory.mk hv)).symm ≪≫
        (coherentStraighteningRestrictionDiagramIso F U g h).symm := rfl
  have hn := coherentStraighteningCounit_baseChange_naturality F U g h
  let E := evaluateFunctorAt (Y := (ihom B).obj SpaceInfinity.{u}) (functorVertex F)
  have hEL := coherentFamilyCurryMap_evaluate_vertex C (functorVertex F)
  have hER := coherentFamilyCurryMap_evaluate_vertex U (functorVertex F)
  have hEV := evaluateFunctorAt_functorVertex (functorVertex F)
    (universalCoherentReconstructionMap B)
  have hEI := evaluateFunctorAt_functorVertex (functorVertex F)
    (𝟙 ((ihom B).obj SpaceInfinity.{u}))
  let q := congrArg (fun d ↦ functorVertex d)
    (curry_uncurry (𝟙 ((ihom B).obj SpaceInfinity.{u})))
  have hl : (eqToIso (congrArg SSet.HomotopyCategory.mk hv)).symm ≪≫
      (eqToIso (congrArg SSet.HomotopyCategory.mk hEL)).symm =
      (eqToIso (congrArg SSet.HomotopyCategory.mk hEV)).symm := by
    exact eqToIso_trans (congrArg SSet.HomotopyCategory.mk hv).symm
      (congrArg SSet.HomotopyCategory.mk hEL).symm
  have hr : eqToIso (congrArg SSet.HomotopyCategory.mk hER) ≪≫
      eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (functorVertex d)) h) =
      VertexIso.map (eqToIso (congrArg SSet.HomotopyCategory.mk q)) E ≪≫
      eqToIso (congrArg SSet.HomotopyCategory.mk hEI) := by
    rw [vertexIso_map_eqToIso q E]
  have hf : (universalCoherentReconstructionCounitIso B).app (functorVertex F) =
      (eqToIso (congrArg SSet.HomotopyCategory.mk hv)).symm ≪≫
      ((eqToIso (congrArg SSet.HomotopyCategory.mk hEL)).symm ≪≫
        VertexIso.map (coherentFamilyCurryIso (coherentStraighteningCounit U)) E ≪≫
        eqToIso (congrArg SSet.HomotopyCategory.mk hER)) ≪≫
      eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (functorVertex d)) h) := by
    rw [FunctorIso.app_eq_evaluate]
    change (eqToIso (congrArg SSet.HomotopyCategory.mk hEV)).symm ≪≫
      VertexIso.map (coherentFamilyCurryIso (coherentStraighteningCounit U) ≪≫
        eqToIso (congrArg SSet.HomotopyCategory.mk q)) E ≪≫
      eqToIso (congrArg SSet.HomotopyCategory.mk hEI) = _
    rw [vertexIso_map_trans]
    conv_lhs => rw [← hl]
    simp only [Iso.trans_assoc]
    conv_lhs => rw [← hr]
  rw [hf, coherentFamilyCurryIso_evaluate]
  rw [hc, ← hn]
  simp [Iso.trans_assoc, g]

end SerrePositivity.InfinityCategories
