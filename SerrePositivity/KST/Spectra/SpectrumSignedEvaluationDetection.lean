module

public import SerrePositivity.KST.Spectra.SpectrumSignedEvaluationSource
public import SerrePositivity.KST.Spectra.SpectrumEvaluationParameterDetection

/-!
概要：実評価由来の BF 比較の π 同型性で、元の Kan 円評価自身の π 同型性を検出する。
方針：元の源への前合成を Whitehead で、BF 射影と sourceMap を全単射 RLP で消去する。
規約：実比較の同値性は仮定として残す。使われ方：全 Hom 比較ホモトピーの最後の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
open RawSpectrumMapping

local instance evaluationDetectionKan (K : PointedSimplicialSet.{u})
    (X Y : OmegaSpectrum.{u}) :
    KanComplex ((ihom K).obj
      (RawSpectrumMapping.pointedSpace (cotensor K X) Y.toKanSequence)).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 元の源へ戻した実評価由来の符号付き写像は、元の Kan 円評価と同じ π 同型性を持つ。 -/
lemma signedEvaluationSource_piIsomorphism_iff (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (signedEvaluationSource X Y).right ↔
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (evaluationPost CirclePower.space.{u} X Y).right := by
  have hp := pointedPre_piIsomorphism_of_levelwise (originalLoopModelMap X)
    (originalLoopModelMap_levelwise X) (KanSequence.signedLoopTail Y.toKanSequence)
  constructor
  · intro h
    exact (signedEvaluationPost_piIsomorphism_iff X Y).mp
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp h hp)
  · intro h
    exact ((signedEvaluationPost_piIsomorphism_iff X Y).mpr h).comp hp

/-- 実際の BF 比較族の π 同型性は、元の Kan 円評価自身の π 同型性と同値。 -/
lemma signedEvaluationCompatibleSource_piIsomorphism_iff (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (signedEvaluationCompatibleSource X Y).right ↔
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (evaluationPost CirclePower.space.{u} X Y).right := by
  have hq : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (pointedPost X (signedLoopProjection Y)).right :=
    post_piIsomorphism X (signedLoopProjection Y)
      (fun n => (Y.toKanSequence.signedLoopTail.replacementStage n).projection_rlp)
  have hs : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (sourceMap CirclePower.space.{u} X Y).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _
      (sourceMap_trivialKanFibration CirclePower.space.{u} X Y).mem
  have hc := congrArg Under.Hom.right (signedEvaluationCompatibleSource_projection X Y)
  constructor
  · intro h
    have hcomp := h.comp hq
    rw [Under.comp_right, Under.comp_right] at hc
    rw [hc] at hcomp
    exact (signedEvaluationSource_piIsomorphism_iff X Y).mp
      ((_root_.SerrePositivity.KST.Spectra.KanPiIsomorphism.cancel_left_atVertex hs) hcomp (pointedSpace CirclePower.space.{u} X Y).basepoint)
  · intro h
    have hcomp := hs.comp ((signedEvaluationSource_piIsomorphism_iff X Y).mpr h)
    rw [Under.comp_right, Under.comp_right] at hc
    rw [← hc] at hcomp
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp hcomp hq

/-- 実際の BF 比較族は、通常の円による元の評価自身の π 同型性も検出する。 -/
lemma signedEvaluationCompatibleSource_circle_piIsomorphism_iff (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (signedEvaluationCompatibleSource X Y).right ↔
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (evaluationPost PointedSimplicialSet.circle.{u} X Y).right :=
  (signedEvaluationCompatibleSource_piIsomorphism_iff X Y).trans
    (evaluationPost_piIsomorphism_iff_of_anodyne CirclePower.unit
      (PointedKanReplacement.unit_anodyne PointedSimplicialSet.circle) X Y).symm

/-- 残る実比較の全 Hom ホモトピーがあれば、通常の円の元の評価自身が π 同型となる。 -/
lemma evaluationPost_circle_piIsomorphism_of_comparison_homotopy (X Y : OmegaSpectrum.{u})
    {B : PointedSimplicialSet.{u}} (j : B ⟶ pointedSpace CirclePower.space.{u} X Y)
    [Mono j.right]
    (H : SSet.Homotopy (signedEvaluationCompatibleSource X Y).right
      (kanAdjointRelativeTracedBFComparison X Y
        (sourceMap CirclePower.space.{u} X Y) j).right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (evaluationPost PointedSimplicialSet.circle.{u} X Y).right :=
  (signedEvaluationCompatibleSource_circle_piIsomorphism_iff X Y).mp
    ((kanPiIsomorphism_iff_of_homotopy H).mpr
      (signedEvaluationCompatibleTracedComparison_piIsomorphism X Y j))

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
