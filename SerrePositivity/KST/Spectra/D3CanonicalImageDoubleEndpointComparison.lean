module

public import SerrePositivity.KST.Spectra.D3DoubleEndpointUnitPasting

/-!
概要：元の canonical image 族を、同じ二方向実端点図式へ指定単位を保って接続する。
方針：元の端点円表示同型へ同じ厳密切断を後合成し、指定実面模型比較へ貼る。
規約：比較・切断・単位を選び直さない。保持済み模型比較との一致は別途証明する。
使われ方：looped canonical と canonical image の双方を同じ実二方向模型で照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 通常 loop の canonical image を、第一パラメータが端点円の実面へ接続する。 -/
def d3CanonicalImageLeftDiagramIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (pointedKanLoopInfinity.{u} ≫ d3PointedKanLoopSection)
      (d3DoubleEndpointRightLoopFamily 0 0) :=
  d3PointedKanEndpointLoopIso.postcomp d3PointedKanLoopSection ≪≫
    d3DoubleEndpointRightModelIso 0 0

/-- 第二パラメータが端点円の実面へも、同じ端点円表示・切断から接続する。 -/
def d3CanonicalImageRightDiagramIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (pointedKanLoopInfinity.{u} ≫ d3PointedKanLoopSection)
      (d3DoubleEndpointLeftLoopFamily 0 0) :=
  d3PointedKanEndpointLoopIso.postcomp d3PointedKanLoopSection ≪≫
    d3DoubleEndpointLeftModelIso 0 0

/-- 同じ端点円表示へ切断を後合成した比較は、厳密終点で元の表示そのもの。 -/
lemma d3EndpointLoopIso_section_target :
    HEq ((d3PointedKanEndpointLoopIso.{u}.postcomp d3PointedKanLoopSection).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)) d3PointedKanEndpointLoopIso := by
  refine (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp d3PointedKanEndpointLoopIso.{u}
    d3PointedKanLoopSection (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))).trans ?_
  refine (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_map_eq d3PointedKanEndpointLoopIso.{u}
    d3PointedKanLoopSection_target.symm).trans ?_
  exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_id d3PointedKanEndpointLoopIso.{u})

/-- 左 canonical image 比較の終点は、元の端点円表示と指定右単位比較の合成。 -/
lemma d3CanonicalImageLeftDiagramIso_target :
    HEq (d3CanonicalImageLeftDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
      (d3PointedKanEndpointLoopIso ≪≫ d3DoubleEndpointRightTargetIso 0 0) := by
  rw [d3CanonicalImageLeftDiagramIso, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans]
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIso_trans_heq_of_heq
    (by rw [Category.assoc, d3PointedKanLoopSection_target, Category.comp_id])
    (by rw [Category.assoc, d3PointedKanLoopSection_target, Category.comp_id]) rfl
    _ _ _ _ d3EndpointLoopIso_section_target (d3KanLoopDiagramIsoOverTarget_target_heq _ _ _)

/-- 右 canonical image 比較の終点も、同じ端点円表示と指定左単位比較を保持。 -/
lemma d3CanonicalImageRightDiagramIso_target :
    HEq (d3CanonicalImageRightDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
      (d3PointedKanEndpointLoopIso ≪≫ d3DoubleEndpointLeftTargetIso 0 0) := by
  rw [d3CanonicalImageRightDiagramIso, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans]
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIso_trans_heq_of_heq
    (by rw [Category.assoc, d3PointedKanLoopSection_target, Category.comp_id])
    (by rw [Category.assoc, d3PointedKanLoopSection_target, Category.comp_id]) rfl
    _ _ _ _ d3EndpointLoopIso_section_target (d3KanLoopDiagramIsoOverTarget_target_heq _ _ _)

/-- 保持済み canonical image 族は、同じ厳密切断の通常 loop 前合成への終点入力。 -/
lemma commonChosenStageCanonicalImageFamily_section (n : ℕ) :
    (commonChosenStageLoopDiagramFamily.{u} (n + 1) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) ≫
        (pointedKanLoopInfinity ≫ d3PointedKanLoopSection) =
    commonChosenStageCanonicalImageFamily n := by
  dsimp only [commonChosenStageCanonicalImageFamily, d3LoopCanonicalFamily]
  rw [commonChosenStageLoopImageFamily_corner]
  simp only [Category.assoc]

/-- 保持済み canonical image 段模型も、同じ終点入力の同じ実右面へ接続する。 -/
def commonChosenStageCanonicalImageDoubleEndpointIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (commonChosenStageCanonicalImageFamily.{u} n)
      ((commonChosenStageLoopDiagramFamily (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) ≫ d3DoubleEndpointRightLoopFamily 0 0) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3CanonicalImageLeftDiagramIso.precomp
    (commonChosenStageLoopDiagramFamily (n + 1) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
    (commonChosenStageCanonicalImageFamily_section n) rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
