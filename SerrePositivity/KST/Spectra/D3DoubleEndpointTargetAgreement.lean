module

public import SerrePositivity.KST.Spectra.D3UnitLoopSourceNaturality
public import SerrePositivity.KST.Spectra.D3CanonicalImageDoubleEndpointComparison

/-!
概要：二方向実模型への二つの接続が、元の同じ指定終点比較を保持すると認証する。
方針：指定単位面の始点自然性と、全四隅の元の比較値を貼る。
規約：元の比較を選び直さない。使われ方：保持済み模型比較との全図式照合。
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

/-- 元の端点図式始点の表示は、元の端点円表示の同じ指定値。 -/
lemma d3PointedKanEndpointSourceIso_value :
    HEq d3PointedKanEndpointLoopDiagram_sourceIso.{u} d3PointedKanEndpointLoopIso.{u} := by
  unfold d3PointedKanEndpointLoopDiagram_sourceIso
  exact targetRewrite_heq (d3PointedKanEndpointLoopDiagram_corner.{u} 0 0)
    d3PointedKanEndpointLoopIso.{u}

/-- 右指定終点は、同じ右単位子の制限そのもの。 -/
lemma d3DoubleEndpointRightTargetIso_value (i j : Fin 2) :
    HEq (d3DoubleEndpointRightTargetIso.{u} i j)
      (d3PointedKanPreFunctorIso (ρ_ (d3EndpointParameterObj.{u} (i, j))).hom) := by
  unfold d3DoubleEndpointRightTargetIso
  refine (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).trans ?_
  rw [d3PointedKanPreFunctorIso_inv, Iso.symm_symm_eq]

/-- 切断補正の loop 像の終点は、元の単位比較の同じ loop 像。 -/
lemma d3LoopedSectionDiagramIso_target_unit :
    HEq (d3LoopedSectionDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)) d3PointedKanUnitLoopIso.{u} := by
  have hs := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq
    (d3PointedKanLoopSection_diagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
    d3PointedKanLoopSection_target rfl).symm.trans
    ((heq_of_eq d3PointedKanLoopSection_diagramIso_target.{u}).trans
      d3PointedKanEndpointTargetIso_value)
  refine (d3LoopedSectionDiagramIso_corner 1 1).trans ?_
  refine (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq d3PointedKanUnitFunctorIso.{u}.symm _
    d3PointedKanLoopSection_target.symm
    (d3PointedKanEndpointLoopDiagram_corner 1 1).symm hs pointedKanLoopInfinity).trans ?_
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm

/-- 左全図式接続の終点は、同じ元の単位面三角形の左辺。 -/
lemma d3LoopedSectionLeftDiagramIso_target_triangle :
    HEq (d3LoopedSectionLeftDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
      (d3PointedKanUnitLoopIso.{u} ≪≫ d3LeftUnitFaceSourceIso) := by
  rw [d3LoopedSectionLeftDiagramIso, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans]
  apply _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIso_trans_heq_of_heq d3LoopedSectionFamily_target.symm
    (by rw [d3EndpointLoopImageFamily_corner, d3PointedKanEndpointLoopDiagram_corner]; rfl)
    (by rw [d3DoubleEndpointLeftLoopFamily_corner,
      d3DoubleEndpointRightLoopFamily_corner])
    _ _ _ _ d3LoopedSectionDiagramIso_target_unit
  exact (d3DoubleEndpointLeftLoopImageDiagramIso_corner 1 1).trans
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _)

/-- 同じ実模型への左接続は、同じ元の端点表示・右単位子を終点に保持する。 -/
lemma d3LoopedSectionLeftDiagramIso_target_value :
    HEq (d3LoopedSectionLeftDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
      (d3PointedKanEndpointLoopIso.{u} ≪≫
        d3PointedKanPreFunctorIso (ρ_ endpointCircle.{u}).hom) := by
  refine d3LoopedSectionLeftDiagramIso_target_triangle.trans ?_
  rw [d3PointedKanUnitFace_source_triangle]
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIso_trans_heq_of_heq rfl
    (d3PointedKanEndpointLoopDiagram_corner 0 0).symm
    (d3DoubleEndpointLeftLoopFamily_corner 1 1 0 0).symm
    _ _ _ _ d3PointedKanEndpointSourceIso_value
    (d3EndpointRightUnitDiagramIso_corner 0 0)

/-- canonical image 側の同じ接続も、同じ端点表示・右単位子を終点に保持する。 -/
lemma d3CanonicalImageLeftDiagramIso_target_value :
    HEq (d3CanonicalImageLeftDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
      (d3PointedKanEndpointLoopIso.{u} ≪≫
        d3PointedKanPreFunctorIso (ρ_ endpointCircle.{u}).hom) := by
  refine d3CanonicalImageLeftDiagramIso_target.trans ?_
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIso_trans_heq_of_heq rfl rfl
    (d3DoubleEndpointRightLoopFamily_corner 0 0 1 1).symm
    _ _ _ _ (HEq.rfl) (d3DoubleEndpointRightTargetIso_value 0 0)

/-- 同じ実右面への二つの接続は、終点表示を揃える前から同じ指定値を持つ。 -/
lemma d3DoubleEndpointLeftConnections_target_agreement :
    HEq (d3LoopedSectionLeftDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
      (d3CanonicalImageLeftDiagramIso.{u}.postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)) := by
  exact d3LoopedSectionLeftDiagramIso_target_value.trans
    d3CanonicalImageLeftDiagramIso_target_value.symm

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
