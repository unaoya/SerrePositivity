module

public import SerrePositivity.KST.Spectra.D3LoopImageComparisonCorners

/-!
概要：元の厳密切断補正の loop 像を、同じ全図式比較の各角で厳密に回収する。
方針：包含の充満忠実性と指定値の前後合成則を使い、元の比較の loop 像へ戻す。
規約：切断補正・比較の値を選び直さない。使われ方：保持した段単位と補正の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 元の切断補正の loop 像を持ち上げた全図式比較は、元の全四角形比較を回収。 -/
lemma d3LoopedSectionDiagramIso_projection :
    HEq (d3LoopedSectionDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι) d3LoopedSectionSquareIso := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).preimageNormalizedFunctorIso_postcomp_heq
        d3LoopedSectionFamily d3EndpointLoopImageFamily d3LoopedSectionSquareIso
        d3LoopedSectionFamily_ι.symm d3EndpointLoopImageFamily_ι.symm

/-- 元の切断補正の loop 像の各角は、元の同じ切断補正の角の通常 loop 像。 -/
lemma d3LoopedSectionSquareIso_corner (i j : Fin 2) :
    HEq (d3LoopedSectionSquareIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)))
      ((d3PointedKanLoopSection_diagramIso.postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j)).postcomp pointedKanLoopInfinity) := by
  unfold d3LoopedSectionSquareIso
  refine (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq _ _ _ _).trans ?_
  refine (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp _ _ _)).trans ?_
  have hp : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι ≫
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map pointedKanLoopInfinity) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j) =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j ≫ pointedKanLoopInfinity := by
    rw [Category.assoc, d3SquareEvaluation_postcomp]
    rfl
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_map_eq _ hp).trans
    (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp d3PointedKanLoopSection_diagramIso.{u}
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j) pointedKanLoopInfinity)).symm

/-- 実 loop 図式上の比較も、同じ元の切断補正の角を通常 loop で写した値を保持。 -/
lemma d3LoopedSectionDiagramIso_corner (i j : Fin 2) :
    HEq (d3LoopedSectionDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j))
      ((d3PointedKanLoopSection_diagramIso.postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j)).postcomp pointedKanLoopInfinity) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq d3LoopedSectionSquareIso _
    d3LoopedSectionFamily_ι.symm d3EndpointLoopImageFamily_ι.symm
    d3LoopedSectionDiagramIso_projection
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j))
  exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp d3LoopedSectionDiagramIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)))).symm.trans
      (h.trans (d3LoopedSectionSquareIso_corner i j))

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
