module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimitHomPiZero
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.TensorPiZeroNaturality

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

namespace SerrePositivity.ComplexLimits

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra _root_.Opposite
open _root_.SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.DiagramModel

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

set_option maxHeartbeats 300000 in
-- 反対圏の局所化と具体的な mate の型の照合で標準の elaboration 上限を超えるため。
/-- 概要：計算対象への Hom と右錐の π₀ の比較は図式に自然（Hovey §5.4）。
方針：同じ右 frame の係数射の実現と unop の合成順序を照合する。
規約：始域の置換は既存の同じ比較射で消す。
使われ方：実際の計算関手の導来 Hom の自然性。 -/
lemma framedLimitHomPiZeroEquiv_target (Y : (Complex A))
    {F G : K ⥤ (Complex A)} (g : F ⟶ G)
    (z : SSet.π₀ ((_root_.SerrePositivity.ComplexLimits.framedLimitConeSpace A K Y).obj F)) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let Q := (weakEquivalences (Complex A)).Q
    _root_.SerrePositivity.ComplexLimits.framedLimitHomPiZeroEquiv A K Y G
        (SSet.mapπ₀ ((_root_.SerrePositivity.ComplexLimits.framedLimitConeSpace A K Y).map g) z) =
      _root_.SerrePositivity.ComplexLimits.framedLimitHomPiZeroEquiv A K Y F z ≫ Q.map ((_root_.SerrePositivity.ComplexLimits.framedLimitFunctor A K).map g) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let Q := (weakEquivalences (Complex A)).Q
  have : Q.op.IsLocalization (weakEquivalences (Complex A)ᵒᵖ) := by
    rw [weakEquivalences_op]
    infer_instance
  have := _root_.SerrePositivity.ComplexLimits.framedLimitProbe_cofibrant A Y
  have : IsFibrant (op (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A Y)) := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fibrantOp_of_cofibrant _
  let e (F : K ⥤ (Complex A)) :=
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv Kᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
      (_root_.SerrePositivity.ComplexLimits.rightFrameDiagram A K F) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K)
      (fun k => _root_.SerrePositivity.ComplexLimits.rightFrame_cofibrant A (F.obj k.unop))
      (fun k _ _ f => _root_.SerrePositivity.ComplexLimits.rightFrame_homotopicallyConstant A (F.obj k.unop) f) Q.op
      (op (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A Y))
  let a : _root_.SerrePositivity.ComplexLimits.rightFrameDiagram A K G ⟶ _root_.SerrePositivity.ComplexLimits.rightFrameDiagram A K F :=
    (_root_.SerrePositivity.ComplexLimits.rightFrameDiagramFamily A K).map g.op
  have hn' := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.frameConePiZeroLocalizationEquiv_source Kᵒᵖ
    (C := (Complex A)ᵒᵖ) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
    (B := _root_.SerrePositivity.ComplexLimits.rightFrameDiagram A K G) (B' := _root_.SerrePositivity.ComplexLimits.rightFrameDiagram A K F)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K)
    (fun k => _root_.SerrePositivity.ComplexLimits.rightFrame_cofibrant A (G.obj k.unop))
    (fun k => _root_.SerrePositivity.ComplexLimits.rightFrame_cofibrant A (F.obj k.unop))
    (fun k _ _ f => _root_.SerrePositivity.ComplexLimits.rightFrame_homotopicallyConstant A (G.obj k.unop) f)
    (fun k _ _ f => _root_.SerrePositivity.ComplexLimits.rightFrame_homotopicallyConstant A (F.obj k.unop) f) Q.op a
    (op (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A Y)) z
  have hn : e G (SSet.mapπ₀ ((_root_.SerrePositivity.ComplexLimits.framedLimitConeSpace A K Y).map g) z) =
      Q.op.map ((FrameWeightRealization.map Kᵒᵖ a).app (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)) ≫ e F z := hn'
  have : IsIso (Q.map (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison A Y)) :=
    Localization.inverts Q (weakEquivalences (Complex A)) _
      (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison_quasiIso A Y)
  change (asIso (Q.map (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison A Y))).inv ≫
      (e G (SSet.mapπ₀ ((_root_.SerrePositivity.ComplexLimits.framedLimitConeSpace A K Y).map g) z)).unop ≫ 𝟙 _ =
    ((asIso (Q.map (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison A Y))).inv ≫ (e F z).unop ≫ 𝟙 _) ≫
      Q.map ((_root_.SerrePositivity.ComplexLimits.framedLimitFunctor A K).map g)
  have hu0 := congrArg (fun f : Q.op.obj ((FrameWeightRealization.functor Kᵒᵖ
      (_root_.SerrePositivity.ComplexLimits.rightFrameDiagram A K G)).obj (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)) ⟶
    Q.op.obj (op (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A Y)) => f.unop) hn
  have hmap : ((FrameWeightRealization.map Kᵒᵖ a).app (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)).unop =
      (_root_.SerrePositivity.ComplexLimits.framedLimitFunctor A K).map g := by
    dsimp only [_root_.SerrePositivity.ComplexLimits.framedLimitFunctor, _root_.SerrePositivity.ComplexLimits.framedLimitOpFunctor, Functor.unop_map, Functor.comp_map,
      FrameWeightRealization.family, a, CategoryTheory.evaluation]
  have hu' : (e G (SSet.mapπ₀ ((_root_.SerrePositivity.ComplexLimits.framedLimitConeSpace A K Y).map g) z)).unop =
      (e F z).unop ≫ Q.map (((FrameWeightRealization.map Kᵒᵖ a).app
        (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)).unop) := by
    simpa only [unop_comp, Functor.op_map, Quiver.Hom.unop_op] using hu0
  have hu : (e G (SSet.mapπ₀ ((_root_.SerrePositivity.ComplexLimits.framedLimitConeSpace A K Y).map g) z)).unop =
      (e F z).unop ≫ Q.map ((_root_.SerrePositivity.ComplexLimits.framedLimitFunctor A K).map g) :=
    hu'.trans (congrArg (fun f => (e F z).unop ≫ Q.map f) hmap)
  simpa only [Category.comp_id, Category.assoc] using
    congrArg (fun f : Q.obj (_root_.SerrePositivity.ComplexLimits.framedLimitProbe A Y) ⟶ Q.obj ((_root_.SerrePositivity.ComplexLimits.framedLimitFunctor A K).obj G) =>
      (asIso (Q.map (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison A Y))).inv ≫ f) hu

/-- 概要：定値図式と計算対象の導来 Hom 同値は終域図式に自然（Hovey §5.4）。
方針：同じ右錐の π₀ を介した二つの比較の自然性を合成する。
規約：両側とも元の同じ図式射を局所化する。
使われ方：導来随伴を構成する Hom 同値の終域自然性。 -/
lemma framedLimitDerivedHomEquiv_target (Y : (Complex A))
    {F G : K ⥤ (Complex A)} (g : F ⟶ G) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (Complex A)).Q
    let QD := (weakEquivalences (K ⥤ (Complex A))).Q
    ∀ x : QD.obj ((Functor.const K).obj Y) ⟶ QD.obj F,
      _root_.SerrePositivity.ComplexLimits.framedLimitDerivedHomEquiv A K Y G (x ≫ QD.map g) =
        _root_.SerrePositivity.ComplexLimits.framedLimitDerivedHomEquiv A K Y F x ≫ Q.map ((_root_.SerrePositivity.ComplexLimits.framedLimitFunctor A K).map g) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  dsimp only
  intro x
  obtain ⟨z, rfl⟩ := (_root_.SerrePositivity.ComplexLimits.framedLimitConePiZeroEquiv A K Y F).surjective x
  change _root_.SerrePositivity.ComplexLimits.framedLimitHomPiZeroEquiv A K Y G
      ((_root_.SerrePositivity.ComplexLimits.framedLimitConePiZeroEquiv A K Y G).symm
        (_root_.SerrePositivity.ComplexLimits.framedLimitConePiZeroEquiv A K Y F z ≫ _)) = _
  rw [← _root_.SerrePositivity.ComplexLimits.framedLimitConePiZeroEquiv_target A K Y g z, Equiv.symm_apply_apply]
  simpa only [_root_.SerrePositivity.ComplexLimits.framedLimitDerivedHomEquiv, Equiv.trans_apply, Equiv.symm_apply_apply] using
    _root_.SerrePositivity.ComplexLimits.framedLimitHomPiZeroEquiv_target A K Y g z

end SerrePositivity.ComplexLimits
