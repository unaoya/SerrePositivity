module

public import SerrePositivity.KST.Spectra.D3PathCorrectedComponentValue

/-!
概要：保持した元の厳密 loop 切断補正の終点が、元の指定単位そのものを回収すると認証。
方針：既存 componentIso と exact 表示の一致を同じ元の補正へ代入する。
規約：切断・path・比較・単位を選び直さない。使われ方：二方向模型の指定終点照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra

/-- 同じ始点表示を輸送した標準同型を貼って戻すと、元の指定同型を回収する。 -/
lemma d3FunctorIso_transport_eqToIso_trans {A X : SSet.{u}} {f f' g : A ⟶ X}
    (h : f = f') (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (eqToIso (congrArg
      (fun v : A ⟶ X ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)) h) ≪≫ e) h rfl = e := by
  subst f'
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq, eqToIso_refl, Iso.refl_trans]

namespace OmegaSpectrum.AdjointLoopRelativeBF

/-- 保持済みの切断補正の終点は、元の指定パラメータ単位比較そのもの。 -/
lemma d3PointedKanLoopSection_diagramIso_target :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3PointedKanLoopSection_diagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)) d3PointedKanLoopSection_target rfl =
    d3PointedKanEndpointTargetIso := by
  have h := d3PathCorrectedComponentIso_postcomp d3PointedKanLoopCorrection.{u}
  change d3PointedKanLoopSection_diagramIso.postcomp
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) = _ at h
  rw [h]
  exact d3FunctorIso_transport_eqToIso_trans _ _

end OmegaSpectrum.AdjointLoopRelativeBF
end SerrePositivity.KST.Spectra
