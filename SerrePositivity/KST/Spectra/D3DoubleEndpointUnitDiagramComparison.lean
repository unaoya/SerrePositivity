module

public import SerrePositivity.KST.Spectra.D3ParameterSquareComparison

/-!
概要：元の左右パラメータ単位子を、端点実 loop 全図式と単位面の比較として保持する。
方針：同じパラメータ自然同型の全四角形比較を全部分複体へ持ち上げる。
規約：点ごとの単位値で全自然性を代用しない。円交換因子の直接比較なし。
使われ方：二方向模型比較の終点を、元の単位図式全体で照合する。
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

/-- 元の右単位子の全パラメータ比較を、同じ実二方向単位面へ送る。 -/
def d3EndpointRightUnitSquareIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso d3EndpointParameterSquare.{u}
      (d3DoubleEndpointLeftLoopFamily 1 1 ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3ParameterSquareIso d3DoubleEndpointRightTargetParameterIso) rfl
    (by rw [d3DoubleEndpointLeftLoopFamily_ι, d3DoubleEndpointSquare,
      d3PointedKanBiParameterSquare_left]; rfl)

/-- 元の左単位子の同じ全パラメータ比較も、実単位面へ接続する。 -/
def d3EndpointLeftUnitSquareIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso d3EndpointParameterSquare.{u}
      (d3DoubleEndpointRightLoopFamily 1 1 ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3ParameterSquareIso d3DoubleEndpointLeftTargetParameterIso) rfl
    (by rw [d3DoubleEndpointRightLoopFamily_ι, d3DoubleEndpointSquare,
      d3PointedKanBiParameterSquare_right]; rfl)

/-- 右単位比較を、元の実 loop 図式と同じ実単位面の全図式比較に持ち上げる。 -/
def d3EndpointRightUnitDiagramIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso d3PointedKanEndpointLoopDiagram.{u} (d3DoubleEndpointLeftLoopFamily 1 1) :=
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).preimageFunctorIso
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq d3EndpointRightUnitSquareIso
          d3PointedKanEndpointLoopDiagram_ι.symm rfl)

/-- 左単位も、同じ元の実 loop 全図式上の比較として保持する。 -/
def d3EndpointLeftUnitDiagramIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso d3PointedKanEndpointLoopDiagram.{u} (d3DoubleEndpointRightLoopFamily 1 1) :=
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).preimageFunctorIso
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq d3EndpointLeftUnitSquareIso
          d3PointedKanEndpointLoopDiagram_ι.symm rfl)

/-- 右単位の全四角形比較は、全四隅で元の同じ右単位子の制限作用を回収。 -/
lemma d3EndpointRightUnitSquareIso_corner (i j : Fin 2) :
    HEq (d3EndpointRightUnitSquareIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)))
      (d3PointedKanPreFunctorIso (ρ_ (d3EndpointParameterObj.{u} (i, j))).hom) := by
  unfold d3EndpointRightUnitSquareIso
  refine (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq _ _ _ _).trans ?_
  refine (d3ParameterSquareIso_corner _ i j).trans ?_
  simp only [d3DoubleEndpointRightTargetParameterIso_hom_app]
  rfl

/-- 左単位の全四角形比較も、同じ元の左単位子を各角で保持する。 -/
lemma d3EndpointLeftUnitSquareIso_corner (i j : Fin 2) :
    HEq (d3EndpointLeftUnitSquareIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)))
      (d3PointedKanPreFunctorIso (λ_ (d3EndpointParameterObj.{u} (i, j))).hom) := by
  unfold d3EndpointLeftUnitSquareIso
  refine (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq _ _ _ _).trans ?_
  refine (d3ParameterSquareIso_corner _ i j).trans ?_
  simp only [d3DoubleEndpointLeftTargetParameterIso_hom_app]
  rfl

/-- 右単位の実 loop 全図式比較は、周囲の全四角形で同じ元の比較を回収する。 -/
lemma d3EndpointRightUnitDiagramIso_projection :
    HEq (d3EndpointRightUnitDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι) d3EndpointRightUnitSquareIso := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).preimageNormalizedFunctorIso_postcomp_heq
        d3PointedKanEndpointLoopDiagram (d3DoubleEndpointLeftLoopFamily 1 1)
        d3EndpointRightUnitSquareIso d3PointedKanEndpointLoopDiagram_ι.symm rfl

/-- 左単位の実全図式比較も、同じ元の全四角形比較の指定値を保持する。 -/
lemma d3EndpointLeftUnitDiagramIso_projection :
    HEq (d3EndpointLeftUnitDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι) d3EndpointLeftUnitSquareIso := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).preimageNormalizedFunctorIso_postcomp_heq
        d3PointedKanEndpointLoopDiagram (d3DoubleEndpointRightLoopFamily 1 1)
        d3EndpointLeftUnitSquareIso d3PointedKanEndpointLoopDiagram_ι.symm rfl

/-- 右単位の実全図式比較は、各角で元の同じ右単位子を回収する。 -/
lemma d3EndpointRightUnitDiagramIso_corner (i j : Fin 2) :
    HEq (d3EndpointRightUnitDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j))
      (d3PointedKanPreFunctorIso (ρ_ (d3EndpointParameterObj.{u} (i, j))).hom) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq d3EndpointRightUnitSquareIso _
    d3PointedKanEndpointLoopDiagram_ι.symm rfl d3EndpointRightUnitDiagramIso_projection
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j))
  exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp d3EndpointRightUnitDiagramIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)))).symm.trans
      (h.trans (d3EndpointRightUnitSquareIso_corner i j))

/-- 左単位も、実全図式の全四隅で元の同じ左単位子を保持する。 -/
lemma d3EndpointLeftUnitDiagramIso_corner (i j : Fin 2) :
    HEq (d3EndpointLeftUnitDiagramIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j))
      (d3PointedKanPreFunctorIso (λ_ (d3EndpointParameterObj.{u} (i, j))).hom) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq d3EndpointLeftUnitSquareIso _
    d3PointedKanEndpointLoopDiagram_ι.symm rfl d3EndpointLeftUnitDiagramIso_projection
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j))
  exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp d3EndpointLeftUnitDiagramIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)))).symm.trans
      (h.trans (d3EndpointLeftUnitSquareIso_corner i j))

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
