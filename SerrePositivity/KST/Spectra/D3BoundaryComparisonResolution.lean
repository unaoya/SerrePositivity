module

public import SerrePositivity.KST.Spectra.D3ComparisonOutput
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathFamilyIso
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport

/-!
概要：元の BF 比較・実 loop 図式・厳密終点と、始点間の可逆比較を同時に保持する。
方針：両端評価を同じ図式基底の refined 始点と実図式始点へ引き戻す。
規約：射影の RLP は未証明。可逆 path の Kan 性から自明性を推論しない。
使われ方：代替経路の境界付き比較問題と、その解から B への厳密な帰着。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance boundaryComparisonSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 比較 path の両端を同時に記憶する射影。 -/
def boundaryComparisonEndpoints : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Sp.{u} ⟶ Sp ⊗ Sp :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Sp 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Sp 1)

/-- 同じ BF 比較・図式基底上で固定すべき、二つの始点作用の全単体対。 -/
def boundaryComparisonSourcePair : commonLoopDiagramResolution.{u} ⟶ Sp ⊗ Sp :=
  lift commonLoopDiagramRefinedMap
    (commonLoopDiagramFamily ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp 0 0)

/-- 指定 BF 比較・全実図式・厳密終点を保持し、始点比較自体も記憶する共通解像。 -/
def boundaryComparisonResolution : SSet.{u + 1} :=
  pullback boundaryComparisonEndpoints.{u} boundaryComparisonSourcePair

/-- 比較 path だけを忘れ、元の同じ BF 比較・全実図式へ戻る。 -/
def boundaryComparisonProjection : boundaryComparisonResolution.{u} ⟶
    commonLoopDiagramResolution := pullback.snd _ _

/-- 同じ共通解像に記憶した、全パラメータ上の可逆比較そのもの。 -/
def boundaryComparisonPath : boundaryComparisonResolution.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Sp :=
  pullback.fst _ _

lemma boundaryComparisonPath_source :
    boundaryComparisonPath.{u} ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Sp 0 =
      boundaryComparisonProjection ≫ commonLoopDiagramRefinedMap := by
  have h := congrArg (fun m ↦ m ≫ fst Sp Sp) (pullback.condition
    (f := boundaryComparisonEndpoints.{u}) (g := boundaryComparisonSourcePair))
  simpa only [boundaryComparisonEndpoints, boundaryComparisonSourcePair,
    boundaryComparisonPath, boundaryComparisonProjection, Category.assoc, lift_fst] using h

lemma boundaryComparisonPath_target :
    boundaryComparisonPath.{u} ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Sp 1 =
      (boundaryComparisonProjection ≫ commonLoopDiagramFamily) ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp 0 0 := by
  have h := congrArg (fun m ↦ m ≫ snd Sp Sp) (pullback.condition
    (f := boundaryComparisonEndpoints.{u}) (g := boundaryComparisonSourcePair))
  simpa only [boundaryComparisonEndpoints, boundaryComparisonSourcePair,
    boundaryComparisonPath, boundaryComparisonProjection, Category.assoc, lift_snd] using h

/-- 同じ実 loop 全図式は、元の共通 BF 基底の厳密 tail を終点に保つ。 -/
lemma boundaryComparisonDiagram_target :
    (boundaryComparisonProjection.{u} ≫ commonLoopDiagramFamily) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp 1 1 =
    (boundaryComparisonProjection ≫ commonLoopDiagramProjection) ≫ commonNativeLoopEndpoint := by
  rw [Category.assoc, commonLoopDiagramFamily_target, Category.assoc]

/-- 元の BF 比較射も、同じ指定値のまま共通解像へ前合成して保持する。 -/
def boundaryComparisonBFIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (boundaryComparisonProjection.{u} ≫ commonLoopDiagramRefinedMap)
      ((boundaryComparisonProjection ≫ commonLoopDiagramProjection) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonMiddleEnriched) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (commonLoopDiagramComparisonIso.precomp boundaryComparisonProjection)
    rfl (Category.assoc _ _ _).symm

/-- 記憶した全 path は、全 Hom・全単体を持つ同じ始点関手間の FunctorIso を与える。 -/
def boundaryComparisonSourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (boundaryComparisonProjection.{u} ≫ commonLoopDiagramRefinedMap)
      ((boundaryComparisonProjection ≫ commonLoopDiagramFamily) ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp 0 0) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathFamilyIso boundaryComparisonPath)
    boundaryComparisonPath_source boundaryComparisonPath_target

/-- 同じ指定図式切断上の比較解から、要求された B の実値を全図式で得る。 -/
def nativeLoopComparisonOfBoundarySection
    (s : SimplicialNerve CommonObject.{u} ⟶ boundaryComparisonResolution)
    (hs : s ≫ boundaryComparisonProjection = commonChosenLoopDiagramSection) :
    NativeLoopComparison.{u} := by
  apply nativeLoopComparisonOfChosenSource
  refine _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (boundaryComparisonSourceIso.precomp s) ?_ ?_
  · rw [← Category.assoc, hs, commonLoopDiagramRefinedMap, ← Category.assoc,
      commonChosenLoopDiagramSection_projection, Category.id_comp]
  · rw [← Category.assoc, ← Category.assoc, hs,
      commonChosenLoopDiagramSection_family]
    rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
