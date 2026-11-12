module

public import SerrePositivity.KST.Spectra.D3JointModelStageComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorSpaceCurrying

/-!
概要：指定共同模型比較から、元の端点図式の通常 loop 像と実二方向面の全図式比較を得る。
方針：同じ始点比較を全関手空間で curry し、元の実面を角だけでなく全図式で回収する。
規約：対象ごとの同型から自然性を推論しない。円交換因子の直接比較はしない。
使われ方：既存の looped canonical 模型と実二方向端点図式を接続する実比較。
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

/-- 元の左共同模型比較から得る、同じ全パラメータ上の通常 loop の始点比較。 -/
def d3DoubleEndpointJointLeftSourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((d3PointedKanSquarePair ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram d3EndpointParameter.{u})) ≫
      pointedKanLoopInfinity)
      (d3DoubleEndpointJointLeftLoopFamily ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  d3KanLoopDiagramSourceIsoOverTarget _ _ d3DoubleEndpointJointLeftTargetIso

/-- 右共同模型比較も、元の同じ全パラメータ上の始点比較を与える。 -/
def d3DoubleEndpointJointRightSourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((d3PointedKanSquarePair ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram d3EndpointParameter.{u})) ≫
      pointedKanLoopInfinity)
      (d3DoubleEndpointJointRightLoopFamily ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  d3KanLoopDiagramSourceIsoOverTarget _ _ d3DoubleEndpointJointRightTargetIso

/-- 元の共同始点の curry は、端点全図式の同じ通常 loop 像そのもの。 -/
lemma d3DoubleEndpointJointSource_curry :
    curry ((β_ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) PointedKanInfinity).hom ≫
      ((d3PointedKanSquarePair ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram d3EndpointParameter)) ≫
          pointedKanLoopInfinity)) =
    d3EndpointParameterSquare ≫
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map pointedKanLoopInfinity := by
  rw [← Category.assoc, curry_natural_right]
  rfl

/-- 端点全図式の通常 loop 像を、元の第一パラメータが端点円である実面へ全図式比較。 -/
def d3DoubleEndpointLeftLoopImageSquareIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d3EndpointParameterSquare.{u} ≫
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map pointedKanLoopInfinity)
      (d3DoubleEndpointRightLoopFamily 0 0 ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((d3DoubleEndpointJointLeftSourceIso.precomp
    (β_ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) PointedKanInfinity).hom).curry)
    d3DoubleEndpointJointSource_curry (by
      rw [d3DoubleEndpointJointLeftLoopFamily_corner, ← Category.assoc,
        SymmetricCategory.symmetry, Category.id_comp, curry_uncurry])

/-- 他方の共同比較からも、同じ通常 loop 像を第二パラメータが端点円の実面へ接続。 -/
def d3DoubleEndpointRightLoopImageSquareIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d3EndpointParameterSquare.{u} ≫
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map pointedKanLoopInfinity)
      (d3DoubleEndpointLeftLoopFamily 0 0 ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((d3DoubleEndpointJointRightSourceIso.precomp
    (β_ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) PointedKanInfinity).hom).curry)
    d3DoubleEndpointJointSource_curry (by
      rw [d3DoubleEndpointJointRightLoopFamily_corner, ← Category.assoc,
        SymmetricCategory.symmetry, Category.id_comp, curry_uncurry])

/-- この同じ元の端点図式の loop 像は、実面との全図式比較から実 loop 図式である。 -/
lemma d3EndpointParameterSquare_loop_isLoop (v : PointedKanInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex ((d3EndpointParameterSquare ≫
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map pointedKanLoopInfinity).app _ v) := by
  have e := d3DoubleEndpointLeftLoopImageSquareIso.{u}.toNatIso.app (SSet.HomotopyCategory.mk v)
  apply (d3IsLoopDiagramVertex_iso e).mpr
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex ((d3DoubleEndpointRightLoopFamily 0 0 ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι).app _ v)
  rw [d3DoubleEndpointRightLoopFamily_ι]
  exact d3DoubleEndpointRightFace_isLoop 0 0 v

/-- 同じ元の端点全図式の通常 loop 像を、その全単体作用のまま実 loop 族へ因子化。 -/
def d3EndpointLoopImageFamily : PointedKanInfinity.{u} ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex (d3EndpointParameterSquare ≫
    (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map pointedKanLoopInfinity)
      d3EndpointParameterSquare_loop_isLoop

lemma d3EndpointLoopImageFamily_ι :
    d3EndpointLoopImageFamily.{u} ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι =
    d3EndpointParameterSquare ≫
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map pointedKanLoopInfinity :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 同じ loop 像から実右面への比較を、実 loop 全図式の同じ比較として保持。 -/
def d3DoubleEndpointLeftLoopImageDiagramIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso d3EndpointLoopImageFamily.{u} (d3DoubleEndpointRightLoopFamily 0 0) :=
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).preimageFunctorIso
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq d3DoubleEndpointLeftLoopImageSquareIso
          d3EndpointLoopImageFamily_ι.symm rfl)

/-- 同じ loop 像から実左面への比較も、実 loop 全図式の同じ比較として回収。 -/
def d3DoubleEndpointRightLoopImageDiagramIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso d3EndpointLoopImageFamily.{u} (d3DoubleEndpointLeftLoopFamily 0 0) :=
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).preimageFunctorIso
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq d3DoubleEndpointRightLoopImageSquareIso
          d3EndpointLoopImageFamily_ι.symm rfl)

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
