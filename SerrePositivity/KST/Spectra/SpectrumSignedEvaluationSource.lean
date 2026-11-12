module

public import SerrePositivity.KST.Spectra.SpectrumSignedEvaluationPost
public import SerrePositivity.KST.Spectra.OriginalLoopModelMap
public import SerrePositivity.KST.Spectra.RawSpectrumMappingPreNaturality
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedComparisonIsomorphism

/-!
概要：元の評価を通る符号付き比較を、保存済み Kan 随伴比較と同じ全 Hom へ戻す。
方針：元の loop 模型への射で前合成し、BF 比較と射影の同じ因子分解を使う。
規約：実際の普遍評価からの合成を保持。使われ方：二つの全 Hom 比較のホモトピー照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
open RawSpectrumMapping

/-- 元の評価から得る符号付き比較を、元の BF 源へ戻した同じ全 Hom の射。 -/
def signedEvaluationSource (X Y : OmegaSpectrum.{u}) :
    RawSpectrumMapping.pointedSpace X Y.toKanSequence ⟶
      RawSpectrumMapping.pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence) :=
  signedEvaluationPost X Y ≫
    pointedPre (originalLoopModelMap X) (KanSequence.signedLoopTail Y.toKanSequence)

/-- 元の可換な射から、一段移動・BF 比較・元の源への前合成で得る実際の比較族。 -/
def signedEvaluationCompatibleSource (X Y : OmegaSpectrum.{u}) :
    pointedSpace CirclePower.space.{u} X Y ⟶
      RawSpectrumMapping.pointedSpace X (signedLoopModel Y).toKanSequence :=
  cotensorMap CirclePower.space.{u} X Y ≫
    pointedTail (cotensor CirclePower.space.{u} X)
      (cotensor CirclePower.space.{u} Y).toKanSequence ≫
    pointedPost (tail (cotensor CirclePower.space.{u} X)) (sequenceHom (signedLoopComparison Y)) ≫
    pointedPre (originalLoopModelMap X) (signedLoopModel Y).toKanSequence

/-- BF 比較族の射影全体は、元の evaluationPost を通る同じ符号付き源比較。 -/
lemma signedEvaluationCompatibleSource_projection (X Y : OmegaSpectrum.{u}) :
    signedEvaluationCompatibleSource X Y ≫ pointedPost X (signedLoopProjection Y) =
      sourceMap CirclePower.space.{u} X Y ≫ signedEvaluationSource X Y := by
  have hp := pointedPost_comp_eq (tail (cotensor CirclePower.space.{u} X))
    (sequenceHom (signedLoopComparison Y)) (signedLoopProjection Y) (signedLoopRawComparison Y)
    (signedLoopComparison_projection Y)
  simp only [signedEvaluationCompatibleSource, signedEvaluationSource, Category.assoc]
  rw [← pointedPre_post (originalLoopModelMap X) (signedLoopProjection Y), ← Category.assoc
    (pointedPost (tail (cotensor CirclePower.space.{u} X)) (sequenceHom (signedLoopComparison Y)))]
  erw [hp]
  have hc := congrArg (· ≫ pointedPre (originalLoopModelMap X)
    (KanSequence.signedLoopTail Y.toKanSequence)) (cotensorMap_signedLoopComparison X Y)
  simpa only [Category.assoc] using hc

/-- 同じ始域・標的を持つ保存済みの相対 Kan 随伴 BF 比較は、既に全基点 π 同型。 -/
lemma signedEvaluationCompatibleTracedComparison_piIsomorphism (X Y : OmegaSpectrum.{u})
    {B : PointedSimplicialSet.{u}} (j : B ⟶ pointedSpace CirclePower.space.{u} X Y)
    [Mono j.right] :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (kanAdjointRelativeTracedBFComparison X Y
      (sourceMap CirclePower.space.{u} X Y) j).right :=
  kanAdjointRelativeTracedBFComparison_piIsomorphism X Y
    (sourceMap CirclePower.space.{u} X Y) j
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (sourceMap_trivialKanFibration CirclePower.space.{u} X Y).mem)

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
