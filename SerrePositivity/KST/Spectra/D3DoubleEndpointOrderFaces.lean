module

public import SerrePositivity.KST.Spectra.D3DoubleEndpointOrderComparison
public import SerrePositivity.KST.Spectra.D3DoubleEndpointTargetAgreement

/-!
概要：全四次元比較の各外側面を、元の指定左右単位比較を保つ実面比較へ戻す。
方針：内側終点射影と外側角評価の厳密交換により、同じ指定値を回収する。
規約：比較・模型を選び直さない。使われ方：全四次元比較の始点作用の照合。
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

private lemma symm_heq {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (hf : f = f') (hg : g = g')
    (h : HEq e' e) : HEq e'.symm e.symm := by
  subst f' g'
  cases eq_of_heq h
  rfl

/-- 元の左指定終点は、同じ左単位子の制限そのもの。 -/
lemma d3DoubleEndpointLeftTargetIso_value (i j : Fin 2) :
    HEq (d3DoubleEndpointLeftTargetIso.{u} i j)
      (d3PointedKanPreFunctorIso (λ_ (d3EndpointParameterObj.{u} (i, j))).hom) := by
  unfold d3DoubleEndpointLeftTargetIso
  refine (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).trans ?_
  rw [d3PointedKanPreFunctorIso_inv, Iso.symm_symm_eq]

/-- 元の左右単位面比較の全四隅は、同じ左右指定終点比較の合成値を保持する。 -/
lemma d3DoubleEndpointUnitFacesIso_corner (i j : Fin 2) :
    HEq (d3DoubleEndpointUnitFacesIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j))
      ((d3DoubleEndpointLeftTargetIso.{u} i j).symm ≪≫
        d3DoubleEndpointRightTargetIso i j) := by
  rw [d3DoubleEndpointUnitFacesIso, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_symm]
  apply _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIso_trans_heq_of_heq
    (by rw [d3DoubleEndpointLeftLoopFamily_corner, d3DoubleEndpointRightLoopFamily_corner])
    (d3PointedKanEndpointLoopDiagram_corner i j).symm
    (by rw [d3DoubleEndpointRightLoopFamily_corner, d3DoubleEndpointLeftLoopFamily_corner])
    _ _ _ _
  · exact symm_heq (d3DoubleEndpointLeftTargetIso i j)
      (d3EndpointLeftUnitDiagramIso.postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j))
      (d3PointedKanEndpointLoopDiagram_corner i j).symm
      (by rw [d3DoubleEndpointLeftLoopFamily_corner, d3DoubleEndpointRightLoopFamily_corner])
      ((d3EndpointLeftUnitDiagramIso_corner i j).trans
        (d3DoubleEndpointLeftTargetIso_value i j).symm)
  · exact (d3EndpointRightUnitDiagramIso_corner i j).trans
      (d3DoubleEndpointRightTargetIso_value i j).symm

/-- 同じ全四次元比較の外側角を、元の同じ実左右面へ厳密表示する。 -/
def d3DoubleEndpointOrderFaceIso (i j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d3DoubleEndpointLeftLoopFamily.{u} i j)
      (d3DoubleEndpointRightLoopFamily i j) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3DoubleEndpointOrderComparison.postcomp
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity) i j))
    (d3DoubleEndpointIteratedLeftFamily_corner i j)
    (d3DoubleEndpointIteratedRightFamily_corner i j)

/-- 同じ外側面比較の終点は、同じ元の左右指定終点値の合成。 -/
lemma d3DoubleEndpointOrderFaceIso_target (i j : Fin 2) :
    HEq ((d3DoubleEndpointOrderFaceIso.{u} i j).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
      ((d3DoubleEndpointLeftTargetIso.{u} i j).symm ≪≫
        d3DoubleEndpointRightTargetIso i j) := by
  unfold d3DoubleEndpointOrderFaceIso
  refine (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq _ _ _ _).trans ?_
  refine (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp _ _ _)).trans ?_
  have hm : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity.{u}) i j ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1 =
    d3DoubleEndpointInnerTargetProjection ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j := by
    let := d3PointedKanLoopEvaluation_trivial.{u}
    exact (d3LoopDiagramTrivialImage_corner _ i j).symm
  refine (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_map_eq d3DoubleEndpointOrderComparison hm).symm.trans ?_
  refine (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp _ _ _)).symm.trans ?_
  refine (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq d3DoubleEndpointUnitFacesIso _
    d3DoubleEndpointIteratedLeftFamily_projection.symm
    d3DoubleEndpointIteratedRightFamily_projection.symm
    d3DoubleEndpointOrderComparison_projection
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j)).trans ?_
  exact d3DoubleEndpointUnitFacesIso_corner i j

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
