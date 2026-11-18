module

public import SerrePositivity.EInfinity.BarrattEccles.CarrierFramedLimitNaturality
public import SerrePositivity.EInfinity.BarrattEccles.CarrierFramedLimitConePiZero
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.TensorPiZeroNaturality

/-!
# 元の計算対象の底への導来 Hom の終域自然性

概要：BM 命題 4.1・Hovey §5.4 の底の導来 Hom 同値を元の図式射の後合成に自然にする。
方針：底の実現の π₀ 比較の自然性と同じ底の計算同型の自然性を合成する。
規約：後合成は元の framedLimitFunctor の射を忘却した局所化像。
使われ方：底の一般 homotopy 極限の導来普遍性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra Opposite
open SerrePositivity.DifferentialGraded
open SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

set_option maxHeartbeats 300000 in
-- 反対圏の局所化と具体的な mate の型の照合で標準の elaboration 上限を超えるため。
/-- 概要：計算対象への Hom と右錐の π₀ の比較は図式に自然（Hovey §5.4）。
方針：同じ右 frame の係数射の実現と unop の合成順序を照合する。
規約：始域の置換は既存の同じ比較射で消す。
使われ方：実際の計算関手の導来 Hom の自然性。 -/
lemma carrierFramedLimitHomPiZeroEquiv_target (Y : Complex A)
    {F G : K ⥤ (operad A).Algebra} (g : F ⟶ G)
    (z : SSet.π₀ ((carrierFramedLimitConeSpace A K Y).obj F)) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let Q := (weakEquivalences (Complex A)).Q
    carrierFramedLimitHomPiZeroEquiv A K G Y
        (SSet.mapπ₀ ((carrierFramedLimitConeSpace A K Y).map g) z) =
      carrierFramedLimitHomPiZeroEquiv A K F Y z ≫ Q.map ((framedLimitFunctor A K).map g).hom := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let Q := (weakEquivalences (Complex A)).Q
  have : Q.op.IsLocalization (weakEquivalences (Complex A)ᵒᵖ) := by
    rw [weakEquivalences_op]
    infer_instance
  have := carrierFramedLimitProbe_cofibrant A Y
  have : IsFibrant (op (carrierFramedLimitProbe A Y)) :=
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fibrantOp_of_cofibrant _
  let e (F : K ⥤ (operad A).Algebra) :=
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv Kᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
      (carrierRightFrameDiagram A K F) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K)
      (fun k => carrierRightFrame_cofibrant A (F.obj k.unop))
      (fun k _ _ f => carrierRightFrame_homotopicallyConstant A (F.obj k.unop) f) Q.op
      (op (carrierFramedLimitProbe A Y))
  let a : carrierRightFrameDiagram A K G ⟶ carrierRightFrameDiagram A K F :=
    (carrierRightFrameDiagramFamily A K).map g.op
  have hn' := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv_source Kᵒᵖ
    (C := (Complex A)ᵒᵖ) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
    (B := carrierRightFrameDiagram A K G) (B' := carrierRightFrameDiagram A K F)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K)
    (fun k => carrierRightFrame_cofibrant A (G.obj k.unop))
    (fun k => carrierRightFrame_cofibrant A (F.obj k.unop))
    (fun k _ _ f => carrierRightFrame_homotopicallyConstant A (G.obj k.unop) f)
    (fun k _ _ f => carrierRightFrame_homotopicallyConstant A (F.obj k.unop) f) Q.op a
    (op (carrierFramedLimitProbe A Y)) z
  have hn : e G (SSet.mapπ₀ ((carrierFramedLimitConeSpace A K Y).map g) z) =
      Q.op.map ((FrameWeightRealization.map Kᵒᵖ a).app (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)) ≫ e F z := hn'
  have : IsIso (Q.map (((carrierFramedLimitProbeComparison A).app Y))) :=
    Localization.inverts Q (weakEquivalences (Complex A)) _
      (carrierFramedLimitProbeComparison_quasiIso A Y)
  change (asIso (Q.map ((carrierFramedLimitProbeComparison A).app Y))).inv ≫
      (e G (SSet.mapπ₀ ((carrierFramedLimitConeSpace A K Y).map g) z)).unop ≫
        Q.map (framedLimitCarrierIso A K G).inv =
    ((asIso (Q.map ((carrierFramedLimitProbeComparison A).app Y))).inv ≫ (e F z).unop ≫
      Q.map (framedLimitCarrierIso A K F).inv) ≫ Q.map ((framedLimitFunctor A K).map g).hom
  have hu0 := congrArg (fun f : Q.op.obj ((FrameWeightRealization.functor Kᵒᵖ
      (carrierRightFrameDiagram A K G)).obj (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)) ⟶
    Q.op.obj (op (carrierFramedLimitProbe A Y)) => f.unop) hn
  have hmap : ((FrameWeightRealization.map Kᵒᵖ a).app (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)).unop =
      (carrierFramedLimitFunctor A K).map g := by
    dsimp only [carrierFramedLimitFunctor, carrierFramedLimitOpFunctor, Functor.unop_map,
      Functor.comp_map,
      FrameWeightRealization.family, a, CategoryTheory.evaluation]
  have hu' : (e G (SSet.mapπ₀ ((carrierFramedLimitConeSpace A K Y).map g) z)).unop =
      (e F z).unop ≫ Q.map (((FrameWeightRealization.map Kᵒᵖ a).app
        (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)).unop) := by
    simpa only [unop_comp, Functor.op_map, Quiver.Hom.unop_op] using hu0
  have hu : (e G (SSet.mapπ₀ ((carrierFramedLimitConeSpace A K Y).map g) z)).unop =
      (e F z).unop ≫ Q.map ((carrierFramedLimitFunctor A K).map g) :=
    hu'.trans (congrArg (fun f => (e F z).unop ≫ Q.map f) hmap)
  have hc : Q.map ((carrierFramedLimitFunctor A K).map g) ≫
      Q.map (framedLimitCarrierIso A K G).inv =
    Q.map (framedLimitCarrierIso A K F).inv ≫ Q.map ((framedLimitFunctor A K).map g).hom :=
    (Q.map_comp _ _).symm.trans
      ((congrArg Q.map ((framedLimitCarrierNatIso A K).inv.naturality g)).trans
        (Q.map_comp _ _))
  rw [hu]
  simp only [Category.assoc]
  exact congrArg (fun h => (asIso (Q.map ((carrierFramedLimitProbeComparison A).app Y))).inv ≫
    (e F z).unop ≫ h) hc

/-- 概要：底の導来 Hom 同値は元の図式射の後合成に自然（Hovey §5.4）。
方針：同じ右錐の π₀ からの二つの比較の自然性を合成する。
規約：元の図式射を忘却して局所化した射を使う。
使われ方：底の導来普遍性と元の極限比較の照合。 -/
lemma carrierFramedLimitDerivedHomEquiv_target (Y : Complex A)
    {F G : K ⥤ (operad A).Algebra} (g : F ⟶ G) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let := CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (Complex A)).Q
    let QD := (weakEquivalences (K ⥤ Complex A)).Q
    ∀ x : QD.obj ((Functor.const K).obj Y) ⟶ QD.obj ((Diagram.forget A K).obj F),
      carrierFramedLimitDerivedHomEquiv A K Y G (x ≫ QD.map ((Diagram.forget A K).map g)) =
        carrierFramedLimitDerivedHomEquiv A K Y F x ≫
          Q.map ((framedLimitFunctor A K).map g).hom := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := CarrierDiagram.projectiveModelCategory A K
  dsimp only
  intro x
  obtain ⟨z, rfl⟩ := (carrierFramedLimitConePiZeroEquiv A K Y F).surjective x
  change carrierFramedLimitHomPiZeroEquiv A K G Y
    ((carrierFramedLimitConePiZeroEquiv A K Y G).symm
      (carrierFramedLimitConePiZeroEquiv A K Y F z ≫ _)) =
    carrierFramedLimitHomPiZeroEquiv A K F Y
      ((carrierFramedLimitConePiZeroEquiv A K Y F).symm
        (carrierFramedLimitConePiZeroEquiv A K Y F z)) ≫ _
  rw [← carrierFramedLimitConePiZeroEquiv_target A K Y g z, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  exact carrierFramedLimitHomPiZeroEquiv_target A K Y g z

end SerrePositivity.EInfinity.BarrattEccles
