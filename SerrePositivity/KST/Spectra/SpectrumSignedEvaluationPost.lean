module

public import SerrePositivity.KST.Spectra.SpectrumEvaluationPostRawComparison
public import SerrePositivity.KST.Spectra.RawSpectrumPointedTailEquivalence
public import SerrePositivity.KST.Spectra.RawSpectrumPostWhitehead
public import SerrePositivity.KST.Spectra.SignedLoopTailTwistComparison

/-!
概要：元の円評価を全 Hom のまま一段移動・符号補正し、可換な射の空間の実比較へ同定する。
方針：厳密な cotensor 交換、一段移動と後合成の自然性、元の twist 因子分解を使う。
規約：元の evaluationPost から定義し直さず合成する。使われ方：比較との全 Hom 接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
open RawSpectrumMapping

local instance signedEvaluationOriginalKan (X Y : OmegaSpectrum.{u}) :
    KanComplex ((ihom CirclePower.space.{u}).obj (RawSpectrumMapping.pointedSpace
      (cotensor CirclePower.space.{u} X) Y.toKanSequence)).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 元の Kan 円の評価写像自身を、同じ符号付き一段移動へ送った全 Hom の射。 -/
def signedEvaluationPost (X Y : OmegaSpectrum.{u}) :
    RawSpectrumMapping.pointedSpace X Y.toKanSequence ⟶
      RawSpectrumMapping.pointedSpace (tail (cotensor CirclePower.space.{u} X))
        (KanSequence.signedLoopTail Y.toKanSequence) :=
  rawEvaluationPost CirclePower.space.{u} X Y ≫
    pointedTail (cotensor CirclePower.space.{u} X)
      (KanSequence.mapping CirclePower.space.{u} Y.toKanSequence) ≫
    pointedPost (tail (cotensor CirclePower.space.{u} X))
      (KanSequence.signedLoopTailTwistComparison Y.toKanSequence)

/-- 元の評価写像の π 同型性は、同じ符号付き全 Hom 比較の π 同型性と同値。 -/
lemma signedEvaluationPost_piIsomorphism_iff (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (signedEvaluationPost X Y).right ↔
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (evaluationPost CirclePower.space.{u} X Y).right := by
  have ht := pointedTail_piIsomorphism (cotensor CirclePower.space.{u} X)
    (KanSequence.mapping CirclePower.space.{u} Y.toKanSequence)
    (KanSequence.mapping_omegaCondition CirclePower.space.{u} Y.toKanSequence
      Y.toKanSequence_omega)
  have hp := pointedPost_levelwise_piIsomorphism (tail (cotensor CirclePower.space.{u} X))
    (KanSequence.signedLoopTailTwistComparison Y.toKanSequence)
    (KanSequence.signedLoopTailTwistComparison_levelwise Y.toKanSequence)
  have htp := ht.comp hp
  constructor
  · intro h
    exact (rawEvaluationPost_piIsomorphism_iff CirclePower.space.{u} X Y).mp
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp h htp)
  · intro h
    exact ((rawEvaluationPost_piIsomorphism_iff CirclePower.space.{u} X Y).mpr h).comp htp

/-- 可換な射の空間の一段移動と元の raw 比較は、元の評価を通る全 Hom で厳密に可換。 -/
lemma cotensorMap_signedLoopComparison (X Y : OmegaSpectrum.{u}) :
    cotensorMap CirclePower.space.{u} X Y ≫
      pointedTail (cotensor CirclePower.space.{u} X)
        (cotensor CirclePower.space.{u} Y).toKanSequence ≫
      pointedPost (tail (cotensor CirclePower.space.{u} X)) (signedLoopRawComparison Y) =
    sourceMap CirclePower.space.{u} X Y ≫ signedEvaluationPost X Y := by
  have hp : pointedPost (tail (cotensor CirclePower.space.{u} X)) (signedLoopRawComparison Y) =
      pointedPost (tail (cotensor CirclePower.space.{u} X))
        (KanSequence.tailHom (cotensorProjection CirclePower.space.{u} Y)) ≫
      pointedPost (tail (cotensor CirclePower.space.{u} X))
        (KanSequence.signedLoopTailTwistComparison Y.toKanSequence) := by
    rw [← signedLoopRawComparison_tail_factor]
    exact (pointedFunctor (tail (cotensor CirclePower.space.{u} X))).map_comp _ _
  have h := congrArg (· ≫ pointedTail (cotensor CirclePower.space.{u} X)
      (KanSequence.mapping CirclePower.space.{u} Y.toKanSequence) ≫
    pointedPost (tail (cotensor CirclePower.space.{u} X))
      (KanSequence.signedLoopTailTwistComparison Y.toKanSequence))
    (cotensorMap_projection CirclePower.space.{u} X Y)
  simp only [Category.assoc] at h
  rw [pointedTail_post_assoc, ← hp] at h
  exact h

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
