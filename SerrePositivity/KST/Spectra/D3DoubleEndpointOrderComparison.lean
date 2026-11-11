module

public import SerrePositivity.KST.Spectra.D3IteratedLoopDiagramProjection
public import SerrePositivity.KST.Spectra.D3DoubleEndpointUnitDiagramComparison

/-!
概要：元の左右単位面を固定し、二つの反復実 loop 図式を全四次元図式で比較する。
方針：内側終点射影の全図式 RLP から、同じ単位面比較を充満忠実に持ち上げる。
規約：始点作用を反転と同一視しない。使われ方：保持した二方向補正の幾何的照合。
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

/-- 元の内側終点射影を、反復実 loop 図式全体の同じ射影として保持する。 -/
def d3DoubleEndpointInnerTargetProjection :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity := by
  let := d3PointedKanLoopEvaluation_trivial.{u}
  exact d3LoopDiagramTrivialImage (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)

instance d3DoubleEndpointInnerTargetProjection_trivial :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration d3DoubleEndpointInnerTargetProjection.{u} := by
  let := d3PointedKanLoopEvaluation_trivial.{u}
  unfold d3DoubleEndpointInnerTargetProjection
  infer_instance

/-- 第一順序の内側終点は、元の同じ右単位面族である。 -/
lemma d3DoubleEndpointIteratedLeftFamily_projection :
    d3DoubleEndpointIteratedLeftFamily.{u} ≫ d3DoubleEndpointInnerTargetProjection =
      d3DoubleEndpointRightLoopFamily 1 1 := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι).mp
  rw [Category.assoc, d3DoubleEndpointInnerTargetProjection, d3LoopDiagramTrivialImage_ι,
    ← Category.assoc, d3DoubleEndpointIteratedLeftFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι,
    d3DoubleEndpointIteratedLeftSquare_inner]

/-- 逆順の内側終点も、元の同じ左単位面族を保持する。 -/
lemma d3DoubleEndpointIteratedRightFamily_projection :
    d3DoubleEndpointIteratedRightFamily.{u} ≫ d3DoubleEndpointInnerTargetProjection =
      d3DoubleEndpointLeftLoopFamily 1 1 := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι).mp
  rw [Category.assoc, d3DoubleEndpointInnerTargetProjection, d3LoopDiagramTrivialImage_ι,
    ← Category.assoc, d3DoubleEndpointIteratedRightFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι,
    d3DoubleEndpointIteratedRightSquare_inner]

/-- 同じ元の端点図式を経由する、元の左右単位面の指定全図式比較。 -/
def d3DoubleEndpointUnitFacesIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d3DoubleEndpointRightLoopFamily.{u} 1 1) (d3DoubleEndpointLeftLoopFamily 1 1) :=
  d3EndpointLeftUnitDiagramIso.symm ≪≫ d3EndpointRightUnitDiagramIso

/-- 二つの反復実図式を、指定された同じ単位面比較を終点に持つ全図式比較で接続。 -/
def d3DoubleEndpointOrderComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso d3DoubleEndpointIteratedLeftFamily.{u} d3DoubleEndpointIteratedRightFamily :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration d3DoubleEndpointInnerTargetProjection).preimageFunctorIso
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq d3DoubleEndpointUnitFacesIso
      d3DoubleEndpointIteratedLeftFamily_projection.symm
      d3DoubleEndpointIteratedRightFamily_projection.symm)

/-- 全反復図式比較の内側終点成分は、元の指定左右単位面比較そのもの。 -/
lemma d3DoubleEndpointOrderComparison_projection :
    HEq (d3DoubleEndpointOrderComparison.{u}.postcomp d3DoubleEndpointInnerTargetProjection)
      d3DoubleEndpointUnitFacesIso.{u} := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration
    d3DoubleEndpointInnerTargetProjection).preimageNormalizedFunctorIso_postcomp_heq
      d3DoubleEndpointIteratedLeftFamily d3DoubleEndpointIteratedRightFamily
      d3DoubleEndpointUnitFacesIso d3DoubleEndpointIteratedLeftFamily_projection.symm
      d3DoubleEndpointIteratedRightFamily_projection.symm

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
