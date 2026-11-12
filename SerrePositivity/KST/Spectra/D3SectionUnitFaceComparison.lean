module

public import SerrePositivity.KST.Spectra.D3PointedKanSectionTargetValue

/-!
概要：元の切断補正と右単位図式の比較を、指定単位を持つ同じ実面模型比較へ照合する。
方針：同じ終点値と単位対象の左右単位子の一致を終点評価の充満忠実性で反映する。
規約：元の切断・比較・単位を選び直さず、円交換因子を直接比較しない。
使われ方：二方向模型の指定終点と保持済み模型比較を接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

private def targetRewrite {A X : SSet.{u}} {f g g' : A ⟶ X}
    (h : g = g') (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g') : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g := by
  rw [h]
  exact e

private lemma targetRewrite_heq {A X : SSet.{u}} {f g g' : A ⟶ X}
    (h : g = g') (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g') : HEq (targetRewrite h e) e := by
  subst g'
  rfl

/-- 元の端点指定単位は、同じ通常の単位内部 Hom 比較の逆そのもの。 -/
lemma d3PointedKanEndpointTargetIso_value :
    HEq d3PointedKanEndpointTargetIso.{u} d3PointedKanUnitFunctorIso.{u}.symm := by
  unfold d3PointedKanEndpointTargetIso
  exact targetRewrite_heq (d3PointedKanEndpointLoopDiagram_corner.{u} 1 1)
    d3PointedKanUnitFunctorIso.{u}.symm

/-- 単位内部 Hom の同じ比較を元の厳密切断へ後合成した比較。 -/
def d3PointedKanUnitSectionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso d3PointedKanLoopSection.{u}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u})) ≫
        d3PointedKanLoopSection) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp d3PointedKanUnitFunctorIso.{u}.symm
    d3PointedKanLoopSection) (Category.id_comp _) rfl

/-- 同じ切断後合成の比較は、厳密終点で元の単位比較を回収する。 -/
lemma d3PointedKanUnitSectionIso_target :
    HEq (d3PointedKanUnitSectionIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)) d3PointedKanUnitFunctorIso.{u}.symm := by
  unfold d3PointedKanUnitSectionIso
  refine (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq _ _ _ _).trans ?_
  refine (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp
    d3PointedKanUnitFunctorIso.{u}.symm d3PointedKanLoopSection
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))).trans ?_
  refine (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_map_eq d3PointedKanUnitFunctorIso.{u}.symm
    d3PointedKanLoopSection_target.symm).trans ?_
  exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_id d3PointedKanUnitFunctorIso.{u}.symm)

/-- 単位対象上では、元の指定左単位比較は同じ右単位子の制限そのもの。 -/
lemma d3DoubleEndpointLeftTargetIso_unit :
    HEq (d3DoubleEndpointLeftTargetIso.{u} 1 1)
      (d3PointedKanPreFunctorIso (ρ_ (𝟙_ PointedSimplicialSet.{u})).hom) := by
  unfold d3DoubleEndpointLeftTargetIso
  refine (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).trans ?_
  change HEq (d3PointedKanPreFunctorIso (λ_ (𝟙_ PointedSimplicialSet.{u})).inv).symm _
  rw [d3PointedKanPreFunctorIso_inv, Iso.symm_symm_eq]
  simp only [unitors_equal]
  rfl

/-- 元の切断補正を右単位図式へ貼った比較と、同じ指定単位の実面模型比較は全図式で一致。 -/
lemma d3PointedKanSection_rightUnit_model :
    d3PointedKanLoopSection_diagramIso.{u} ≪≫ d3EndpointRightUnitDiagramIso =
      d3PointedKanUnitSectionIso ≪≫ d3DoubleEndpointLeftModelIso 1 1 := by
  let := d3PointedKanLoopEvaluation_trivial.{u}
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)).postcomp_functorIso_injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans]
  have hs := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq
    (d3PointedKanLoopSection_diagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
    d3PointedKanLoopSection_target rfl).symm.trans
    ((heq_of_eq d3PointedKanLoopSection_diagramIso_target.{u}).trans
      d3PointedKanEndpointTargetIso_value)
  have ha := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIso_trans_heq_of_heq
    d3PointedKanLoopSection_target.symm (d3PointedKanEndpointLoopDiagram_corner 1 1).symm
    (d3DoubleEndpointLeftLoopFamily_corner 1 1 1 1).symm
    d3PointedKanUnitFunctorIso.{u}.symm
    (d3PointedKanPreFunctorIso (ρ_ (𝟙_ PointedSimplicialSet.{u})).hom)
    _ _ hs (d3EndpointRightUnitDiagramIso_corner 1 1)
  have hb := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIso_trans_heq_of_heq d3PointedKanLoopSection_target.symm
    (by
      rw [Category.assoc, d3PointedKanLoopSection_target]
      exact (Category.comp_id _).symm)
    (d3DoubleEndpointLeftLoopFamily_corner 1 1 1 1).symm
    d3PointedKanUnitFunctorIso.{u}.symm
    (d3PointedKanPreFunctorIso (ρ_ (𝟙_ PointedSimplicialSet.{u})).hom)
    _ _ d3PointedKanUnitSectionIso_target
    ((d3KanLoopDiagramIsoOverTarget_target_heq _ _ _).trans d3DoubleEndpointLeftTargetIso_unit)
  exact eq_of_heq (ha.trans hb.symm)

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
