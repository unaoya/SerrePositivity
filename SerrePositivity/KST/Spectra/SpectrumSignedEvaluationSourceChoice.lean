module

public import SerrePositivity.KST.Spectra.SpectrumSignedEvaluationDetection
public import SerrePositivity.KST.Spectra.TracedOriginalLoopModelMap

/-!
概要：元の評価の π 同型性を検出する際、源比較を任意の段ごとの π 同型へ取り替える。
方針：同じ評価由来の中間写像に対し、元の源比較と選んだ源比較の前合成を別々に消去する。
規約：二つの単位の一致は不要。使われ方：実構造区間を保持する源比較での照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
open RawSpectrumMapping

local instance sourceChoiceEvaluationKan (K : PointedSimplicialSet.{u})
    (X Y : OmegaSpectrum.{u}) :
    KanComplex ((ihom K).obj
      (RawSpectrumMapping.pointedSpace (cotensor K X)
        Y.toKanSequence)).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 元の評価由来の同じ BF 比較族に、指定した源比較を前合成する。 -/
def signedEvaluationCompatibleAt (X Y : OmegaSpectrum.{u})
    (e : X ⟶ tail (cotensor CirclePower.space.{u} X)) :
    pointedSpace CirclePower.space.{u} X Y ⟶
      RawSpectrumMapping.pointedSpace X (signedLoopModel Y).toKanSequence :=
  cotensorMap CirclePower.space.{u} X Y ≫
    pointedTail (cotensor CirclePower.space.{u} X)
      (cotensor CirclePower.space.{u} Y).toKanSequence ≫
    pointedPost (tail (cotensor CirclePower.space.{u} X)) (sequenceHom (signedLoopComparison Y)) ≫
    pointedPre e (signedLoopModel Y).toKanSequence

/-- 同じ源比較を、置換前の元の評価由来の比較へ前合成する。 -/
def signedEvaluationAt (X Y : OmegaSpectrum.{u})
    (e : X ⟶ tail (cotensor CirclePower.space.{u} X)) :
    RawSpectrumMapping.pointedSpace X Y.toKanSequence ⟶
      RawSpectrumMapping.pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence) :=
  signedEvaluationPost X Y ≫ pointedPre e (KanSequence.signedLoopTail Y.toKanSequence)

/-- 指定した源比較でも、実際の BF 射影全体は元の評価を通る同じ厳密な式。 -/
lemma signedEvaluationCompatibleAt_projection (X Y : OmegaSpectrum.{u})
    (e : X ⟶ tail (cotensor CirclePower.space.{u} X)) :
    signedEvaluationCompatibleAt X Y e ≫ pointedPost X (signedLoopProjection Y) =
      sourceMap CirclePower.space.{u} X Y ≫ signedEvaluationAt X Y e := by
  have hp := pointedPost_comp_eq (tail (cotensor CirclePower.space.{u} X))
    (sequenceHom (signedLoopComparison Y)) (signedLoopProjection Y) (signedLoopRawComparison Y)
    (signedLoopComparison_projection Y)
  simp only [signedEvaluationCompatibleAt, signedEvaluationAt, Category.assoc]
  rw [← pointedPre_post e (signedLoopProjection Y), ← Category.assoc
    (pointedPost (tail (cotensor CirclePower.space.{u} X)) (sequenceHom (signedLoopComparison Y)))]
  erw [hp]
  have hc := congrArg (· ≫ pointedPre e (KanSequence.signedLoopTail Y.toKanSequence))
    (cotensorMap_signedLoopComparison X Y)
  simpa only [Category.assoc] using hc

/-- 元の源比較を選べば、元の実比較族へ厳密に戻る。 -/
lemma signedEvaluationCompatibleAt_original (X Y : OmegaSpectrum.{u}) :
    signedEvaluationCompatibleAt X Y (originalLoopModelMap X) =
      signedEvaluationCompatibleSource X Y := rfl

/-- どの段ごとの π 同型の源比較を選んでも、通常の円の元の評価を検出する。 -/
lemma signedEvaluationCompatibleAt_circle_piIsomorphism_iff (X Y : OmegaSpectrum.{u})
    (e : X ⟶ tail (cotensor CirclePower.space.{u} X))
    (he : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (e.app n).right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (signedEvaluationCompatibleAt X Y e).right ↔
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (evaluationPost PointedSimplicialSet.circle.{u} X Y).right := by
  have hp := pointedPre_piIsomorphism_of_levelwise e he (signedLoopModel Y).toKanSequence
  have ho := pointedPre_piIsomorphism_of_levelwise (originalLoopModelMap X)
    (originalLoopModelMap_levelwise X) (signedLoopModel Y).toKanSequence
  let b := cotensorMap CirclePower.space.{u} X Y ≫
    pointedTail (cotensor CirclePower.space.{u} X)
      (cotensor CirclePower.space.{u} Y).toKanSequence ≫
    pointedPost (tail (cotensor CirclePower.space.{u} X)) (sequenceHom (signedLoopComparison Y))
  have hb (d : X ⟶ tail (cotensor CirclePower.space.{u} X)) :
      signedEvaluationCompatibleAt X Y d = b ≫ pointedPre d (signedLoopModel Y).toKanSequence := by
    simp only [signedEvaluationCompatibleAt, b, Category.assoc]
  have hbo : signedEvaluationCompatibleSource X Y =
      b ≫ pointedPre (originalLoopModelMap X) (signedLoopModel Y).toKanSequence := by
    simp only [signedEvaluationCompatibleSource, b, Category.assoc]
  constructor
  · intro h
    rw [hb, Under.comp_right] at h
    have hbase := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp h hp
    apply (signedEvaluationCompatibleSource_circle_piIsomorphism_iff X Y).mp
    rw [hbo, Under.comp_right]
    exact hbase.comp ho
  · intro h
    have h0 := (signedEvaluationCompatibleSource_circle_piIsomorphism_iff X Y).mpr h
    rw [hbo, Under.comp_right] at h0
    have hbase := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp h0 ho
    rw [hb, Under.comp_right]
    exact hbase.comp hp

/-- 実構造区間を保持した単位による源比較を使う、元の評価由来の全 Hom 写像。 -/
def tracedSignedEvaluationCompatible (X Y : OmegaSpectrum.{u}) :=
  signedEvaluationCompatibleAt X Y (tracedOriginalLoopModelMap X)

/-- トレース付き源比較を使っても、通常の円の元の評価自身の π 同型性と同値。 -/
lemma tracedSignedEvaluationCompatible_circle_piIsomorphism_iff (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (tracedSignedEvaluationCompatible X Y).right ↔
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (evaluationPost PointedSimplicialSet.circle.{u} X Y).right :=
  signedEvaluationCompatibleAt_circle_piIsomorphism_iff X Y (tracedOriginalLoopModelMap X)
    (tracedOriginalLoopModelMap_levelwise X)

/-- トレース付き源を使う実比較のホモトピーから、元の通常円評価自身へ戻す。 -/
lemma evaluationPost_circle_piIsomorphism_of_traced_comparison_homotopy
    (X Y : OmegaSpectrum.{u})
    {B : PointedSimplicialSet.{u}} (j : B ⟶ pointedSpace CirclePower.space.{u} X Y)
    [Mono j.right]
    (H : SSet.Homotopy (tracedSignedEvaluationCompatible X Y).right
      (kanAdjointRelativeTracedBFComparison X Y
        (sourceMap CirclePower.space.{u} X Y) j).right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (evaluationPost PointedSimplicialSet.circle.{u} X Y).right :=
  (tracedSignedEvaluationCompatible_circle_piIsomorphism_iff X Y).mp
    ((kanPiIsomorphism_iff_of_homotopy H).mpr
      (signedEvaluationCompatibleTracedComparison_piIsomorphism X Y j))

/-- BF 持ち上げの比較ではなく、raw な全 Hom の比較ホモトピーだけでも十分。 -/
lemma evaluationPost_circle_piIsomorphism_of_raw_traced_homotopy
    (X Y : OmegaSpectrum.{u})
    (H : SSet.Homotopy
      (sourceMap CirclePower.space.{u} X Y ≫
        signedEvaluationAt X Y (tracedOriginalLoopModelMap X)).right
      (kanAdjointTracedUnitFamily X Y (sourceMap CirclePower.space.{u} X Y)).right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (evaluationPost PointedSimplicialSet.circle.{u} X Y).right := by
  have hφ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (sourceMap CirclePower.space.{u} X Y).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _
      (sourceMap_trivialKanFibration CirclePower.space.{u} X Y).mem
  have hr := (kanPiIsomorphism_iff_of_homotopy H).mpr
    (kanAdjointTracedUnitFamily_piIsomorphism X Y (sourceMap CirclePower.space.{u} X Y) hφ)
  have hp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (pointedPost X (signedLoopProjection Y)).right :=
    post_piIsomorphism X (signedLoopProjection Y)
      (fun n => (KanSequence.replacementStage (KanSequence.signedLoopTail Y.toKanSequence)
        n).projection_rlp)
  apply (tracedSignedEvaluationCompatible_circle_piIsomorphism_iff X Y).mp
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := (pointedPost X (signedLoopProjection Y)).right) _ hp
  rw [← Under.comp_right]
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((signedEvaluationCompatibleAt X Y (tracedOriginalLoopModelMap X) ≫
    pointedPost X (signedLoopProjection Y)).right)
  rw [signedEvaluationCompatibleAt_projection]
  exact hr

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
