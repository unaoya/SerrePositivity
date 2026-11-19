module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.D3JointSourceStageComparison

/-!
概要：二方向全図式比較の各角が、以前の同じ指定始点比較に一致することを認証する。
方針：元の curry と評価の交換を、共同始点比較の同じ角制限へ合成する。
規約：全 Hom の比較の値を追跡し、点ごとの同型で自然性を代用しない。
使われ方：保持済み模型補正との照合に必要な始点・終点の指定値の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 二方向の左全図式比較の各角は、同じ元の左実面始点比較そのもの。 -/
lemma d3DoubleEndpointLeftLoopImageSquareIso_corner (k l : Fin 2) :
    HEq (d3DoubleEndpointLeftLoopImageSquareIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l)))
      (d3DoubleEndpointLeftSourceIso k l) := by
  unfold d3DoubleEndpointLeftLoopImageSquareIso
  refine (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq _ _ _ _).trans ?_
  refine (d3FunctorIso_curry_postcomp_evaluate _ _).trans ?_
  refine (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorIso_precomp_precomp_heq _ _ _).trans ?_
  have hb : lift (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l))
      (𝟙 PointedKanInfinity.{u}) ≫
      (β_ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) PointedKanInfinity).hom =
    lift (𝟙 PointedKanInfinity)
      (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l)) := rfl
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_heq_of_map_eq _ hb).trans
    (d3DoubleEndpointJointLeftSourceIso_face k l)

/-- 右全図式比較も、各角で同じ元の右実面始点比較の指定値を回収する。 -/
lemma d3DoubleEndpointRightLoopImageSquareIso_corner (k l : Fin 2) :
    HEq (d3DoubleEndpointRightLoopImageSquareIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l)))
      (d3DoubleEndpointRightSourceIso k l) := by
  unfold d3DoubleEndpointRightLoopImageSquareIso
  refine (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq _ _ _ _).trans ?_
  refine (d3FunctorIso_curry_postcomp_evaluate _ _).trans ?_
  refine (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorIso_precomp_precomp_heq _ _ _).trans ?_
  have hb : lift (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l))
      (𝟙 PointedKanInfinity.{u}) ≫
      (β_ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) PointedKanInfinity).hom =
    lift (𝟙 PointedKanInfinity)
      (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l)) := rfl
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_heq_of_map_eq _ hb).trans
    (d3DoubleEndpointJointRightSourceIso_face k l)

/-- 左の実 loop 全図式比較は、周囲の全四角形で元の同じ比較を回収する。 -/
lemma d3DoubleEndpointLeftLoopImageDiagramIso_projection :
    HEq (d3DoubleEndpointLeftLoopImageDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι)
      d3DoubleEndpointLeftLoopImageSquareIso := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).preimageNormalizedFunctorIso_postcomp_heq
        d3EndpointLoopImageFamily (d3DoubleEndpointRightLoopFamily 0 0)
        d3DoubleEndpointLeftLoopImageSquareIso d3EndpointLoopImageFamily_ι.symm rfl

/-- 右の実 loop 全図式比較も、元の同じ全四角形比較の指定値を保持する。 -/
lemma d3DoubleEndpointRightLoopImageDiagramIso_projection :
    HEq (d3DoubleEndpointRightLoopImageDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι)
      d3DoubleEndpointRightLoopImageSquareIso := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).preimageNormalizedFunctorIso_postcomp_heq
        d3EndpointLoopImageFamily (d3DoubleEndpointLeftLoopFamily 0 0)
        d3DoubleEndpointRightLoopImageSquareIso d3EndpointLoopImageFamily_ι.symm rfl

/-- 左の実 loop 図式比較の全四隅は、元の同じ実面始点比較そのもの。 -/
lemma d3DoubleEndpointLeftLoopImageDiagramIso_corner (k l : Fin 2) :
    HEq (d3DoubleEndpointLeftLoopImageDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity k l)) (d3DoubleEndpointLeftSourceIso k l) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq d3DoubleEndpointLeftLoopImageSquareIso _
    d3EndpointLoopImageFamily_ι.symm rfl d3DoubleEndpointLeftLoopImageDiagramIso_projection
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l))
  exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp d3DoubleEndpointLeftLoopImageDiagramIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l)))).symm.trans
      (h.trans (d3DoubleEndpointLeftLoopImageSquareIso_corner k l))

/-- 右の実 loop 図式比較も、全四隅で元の同じ指定比較を回収する。 -/
lemma d3DoubleEndpointRightLoopImageDiagramIso_corner (k l : Fin 2) :
    HEq (d3DoubleEndpointRightLoopImageDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity k l)) (d3DoubleEndpointRightSourceIso k l) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq d3DoubleEndpointRightLoopImageSquareIso _
    d3EndpointLoopImageFamily_ι.symm rfl d3DoubleEndpointRightLoopImageDiagramIso_projection
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l))
  exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp d3DoubleEndpointRightLoopImageDiagramIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l)))).symm.trans
      (h.trans (d3DoubleEndpointRightLoopImageSquareIso_corner k l))

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
