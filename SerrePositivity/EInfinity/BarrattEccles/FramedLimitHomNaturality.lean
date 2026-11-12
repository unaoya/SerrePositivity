module

public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitHomPiZero
public import SerrePositivity.EInfinity.HomotopyWeight.TensorPiZeroNaturality

/-!
# 計算した極限への導来 Hom の終域図式に関する自然性

概要：BM 命題 4.1・Hovey §5.4 の Hom 比較を元の図式射の後合成に自然にする。
方針：反対圏での係数 frame の射による実現の前合成自然性を元の圏へ戻す。
規約：後合成は実際の framedLimitFunctor の同じ射を局所化したもの。
使われ方：定値図式との導来随伴と右導来極限の普遍性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits HomotopicalAlgebra Opposite
open SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

set_option maxHeartbeats 300000 in
-- 反対圏の局所化と具体的な mate の型の照合で標準の elaboration 上限を超えるため。
/-- 概要：計算対象への Hom と右錐の π₀ の比較は図式に自然（Hovey §5.4）。
方針：同じ右 frame の係数射の実現と unop の合成順序を照合する。
規約：始域の置換は既存の同じ比較射で消す。
使われ方：実際の計算関手の導来 Hom の自然性。 -/
lemma framedLimitHomPiZeroEquiv_target (Y : (operad A).Algebra)
    {F G : K ⥤ (operad A).Algebra} (g : F ⟶ G)
    (z : SSet.π₀ ((framedLimitConeSpace A K Y).obj F)) :
    let := modelCategory A
    let Q := (weakEquivalences (operad A).Algebra).Q
    framedLimitHomPiZeroEquiv A K Y G
        (SSet.mapπ₀ ((framedLimitConeSpace A K Y).map g) z) =
      framedLimitHomPiZeroEquiv A K Y F z ≫ Q.map ((framedLimitFunctor A K).map g) := by
  let := modelCategory A
  let Q := (weakEquivalences (operad A).Algebra).Q
  have : Q.op.IsLocalization (weakEquivalences (operad A).Algebraᵒᵖ) := by
    rw [weakEquivalences_op]
    infer_instance
  have := framedLimitProbe_cofibrant A Y
  have : IsFibrant (op (framedLimitProbe A Y)) := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fibrantOp_of_cofibrant _
  let e (F : K ⥤ (operad A).Algebra) :=
    HomotopyWeight.frameConePiZeroLocalizationEquiv Kᵒᵖ (SerrePositivity.EInfinity.HomotopyWeight.framedLimitWeight K)
      (rightFrameDiagram A K F) (SerrePositivity.EInfinity.HomotopyWeight.framedLimitWeight_cofibrant K)
      (fun k => rightFrame_cofibrant A (F.obj k.unop))
      (fun k _ _ f => rightFrame_homotopicallyConstant A (F.obj k.unop) f) Q.op
      (op (framedLimitProbe A Y))
  let a : rightFrameDiagram A K G ⟶ rightFrameDiagram A K F :=
    (rightFrameDiagramFamily A K).map g.op
  have hn' := HomotopyWeight.frameConePiZeroLocalizationEquiv_source Kᵒᵖ
    (C := (operad A).Algebraᵒᵖ) (SerrePositivity.EInfinity.HomotopyWeight.framedLimitWeight K)
    (B := rightFrameDiagram A K G) (B' := rightFrameDiagram A K F)
    (SerrePositivity.EInfinity.HomotopyWeight.framedLimitWeight_cofibrant K)
    (fun k => rightFrame_cofibrant A (G.obj k.unop))
    (fun k => rightFrame_cofibrant A (F.obj k.unop))
    (fun k _ _ f => rightFrame_homotopicallyConstant A (G.obj k.unop) f)
    (fun k _ _ f => rightFrame_homotopicallyConstant A (F.obj k.unop) f) Q.op a
    (op (framedLimitProbe A Y)) z
  have hn : e G (SSet.mapπ₀ ((framedLimitConeSpace A K Y).map g) z) =
      Q.op.map ((FrameWeightRealization.map Kᵒᵖ a).app (SerrePositivity.EInfinity.HomotopyWeight.framedLimitWeight K)) ≫ e F z := hn'
  have : IsIso (Q.map (framedLimitProbeComparison A Y)) :=
    Localization.inverts Q (weakEquivalences (operad A).Algebra) _
      (framedLimitProbeComparison_quasiIso A Y)
  change (asIso (Q.map (framedLimitProbeComparison A Y))).inv ≫
      (e G (SSet.mapπ₀ ((framedLimitConeSpace A K Y).map g) z)).unop ≫ 𝟙 _ =
    ((asIso (Q.map (framedLimitProbeComparison A Y))).inv ≫ (e F z).unop ≫ 𝟙 _) ≫
      Q.map ((framedLimitFunctor A K).map g)
  have hu0 := congrArg (fun f : Q.op.obj ((FrameWeightRealization.functor Kᵒᵖ
      (rightFrameDiagram A K G)).obj (SerrePositivity.EInfinity.HomotopyWeight.framedLimitWeight K)) ⟶
    Q.op.obj (op (framedLimitProbe A Y)) => f.unop) hn
  have hmap : ((FrameWeightRealization.map Kᵒᵖ a).app (SerrePositivity.EInfinity.HomotopyWeight.framedLimitWeight K)).unop =
      (framedLimitFunctor A K).map g := by
    dsimp only [framedLimitFunctor, framedLimitOpFunctor, Functor.unop_map, Functor.comp_map,
      FrameWeightRealization.family, a, CategoryTheory.evaluation]
  have hu' : (e G (SSet.mapπ₀ ((framedLimitConeSpace A K Y).map g) z)).unop =
      (e F z).unop ≫ Q.map (((FrameWeightRealization.map Kᵒᵖ a).app
        (SerrePositivity.EInfinity.HomotopyWeight.framedLimitWeight K)).unop) := by
    simpa only [unop_comp, Functor.op_map, Quiver.Hom.unop_op] using hu0
  have hu : (e G (SSet.mapπ₀ ((framedLimitConeSpace A K Y).map g) z)).unop =
      (e F z).unop ≫ Q.map ((framedLimitFunctor A K).map g) :=
    hu'.trans (congrArg (fun f => (e F z).unop ≫ Q.map f) hmap)
  simpa only [Category.comp_id, Category.assoc] using
    congrArg (fun f : Q.obj (framedLimitProbe A Y) ⟶ Q.obj ((framedLimitFunctor A K).obj G) =>
      (asIso (Q.map (framedLimitProbeComparison A Y))).inv ≫ f) hu

/-- 概要：定値図式と計算対象の導来 Hom 同値は終域図式に自然（Hovey §5.4）。
方針：同じ右錐の π₀ を介した二つの比較の自然性を合成する。
規約：両側とも元の同じ図式射を局所化する。
使われ方：導来随伴を構成する Hom 同値の終域自然性。 -/
lemma framedLimitDerivedHomEquiv_target (Y : (operad A).Algebra)
    {F G : K ⥤ (operad A).Algebra} (g : F ⟶ G) :
    let := modelCategory A
    let := Diagram.projectiveModelCategory A K
    let Q := (weakEquivalences (operad A).Algebra).Q
    let QD := (weakEquivalences (K ⥤ (operad A).Algebra)).Q
    ∀ x : QD.obj ((Functor.const K).obj Y) ⟶ QD.obj F,
      framedLimitDerivedHomEquiv A K Y G (x ≫ QD.map g) =
        framedLimitDerivedHomEquiv A K Y F x ≫ Q.map ((framedLimitFunctor A K).map g) := by
  let := modelCategory A
  let := Diagram.projectiveModelCategory A K
  dsimp only
  intro x
  obtain ⟨z, rfl⟩ := (framedLimitConePiZeroEquiv A K Y F).surjective x
  change framedLimitHomPiZeroEquiv A K Y G
      ((framedLimitConePiZeroEquiv A K Y G).symm
        (framedLimitConePiZeroEquiv A K Y F z ≫ _)) = _
  rw [← framedLimitConePiZeroEquiv_target A K Y g z, Equiv.symm_apply_apply]
  simpa only [framedLimitDerivedHomEquiv, Equiv.trans_apply, Equiv.symm_apply_apply] using
    framedLimitHomPiZeroEquiv_target A K Y g z

end SerrePositivity.EInfinity.BarrattEccles
