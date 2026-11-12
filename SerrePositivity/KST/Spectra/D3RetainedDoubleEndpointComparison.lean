module

public import SerrePositivity.KST.Spectra.D3DoubleEndpointTargetAgreement

/-!
概要：二つの実模型接続の一致を、保持した元の段模型比較へ全図式で戻す。
方針：指定終点比較の一致と、元の終点評価の充満忠実性を使用する。
規約：模型比較・構造補正を選び直さない。使われ方：元の補正を実二方向模型で計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

private lemma eqToIso_trans_heq {C : Type*} [Category C] {a b c : C}
    (h : a = b) (e : b ≅ c) : HEq (eqToIso h ≪≫ e) e := by
  subst b
  simp only [eqToIso_refl, Iso.refl_trans]
  rfl

/-- 元の二つの接続は、各段の同じ終点入力でも指定終点値が一致する。 -/
lemma commonChosenStageDoubleEndpointConnections_target_agreement (n : ℕ) :
    HEq ((commonChosenStageLoopedCanonicalDoubleEndpointIso.{u} n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
      ((commonChosenStageCanonicalImageDoubleEndpointIso.{u} n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)) := by
  unfold commonChosenStageLoopedCanonicalDoubleEndpointIso
    commonChosenStageCanonicalImageDoubleEndpointIso
  refine (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq _ _ _ _).trans ?_
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp]
  refine (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_precomp_heq_of_heq
    (d3CanonicalImageLeftDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
    (d3LoopedSectionLeftDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
    (by rw [Category.assoc, d3PointedKanLoopSection_target,
      Category.comp_id, d3LoopedSectionFamily_target]) rfl
    d3DoubleEndpointLeftConnections_target_agreement _).trans ?_
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp]
  exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq _ _ _ _).symm

/-- 保持した元の段模型比較は、同じ二方向実模型への二つの接続の全図式比較そのもの。 -/
lemma commonChosenStageLoopImageComparison_doubleEndpoint (n : ℕ) :
    commonChosenStageLoopedCanonicalDoubleEndpointIso.{u} n =
      commonChosenStageLoopImageComparison n ≪≫
        commonChosenStageCanonicalImageDoubleEndpointIso n := by
  let := d3PointedKanLoopEvaluation_trivial.{u}
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)).postcomp_functorIso_injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans, commonChosenStageLoopImageComparison_target]
  exact eq_of_heq ((commonChosenStageDoubleEndpointConnections_target_agreement n).trans
    (eqToIso_trans_heq _ _).symm)

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
