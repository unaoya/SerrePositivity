module

public import SerrePositivity.KST.Spectra.SignedLoopSourceComparison
public import SerrePositivity.KST.Spectra.RawSpectrumPointedPostLifting
public import SerrePositivity.KST.Spectra.PointedTrivialVerticalPaths

/-!
概要：源の twist による比較を、元の signedLoopComparison と全 Hom の同じ射影の上で結ぶ。
方針：元の raw 比較への厳密な因子分解と、全 Hom の後合成の全単射 RLP を使う。
規約：段ごとの成分一致から全列ホモトピーを推論しない。
使われ方：HA §1.4.2。元の BF 比較を保持する源の符号補正。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
variable (Z X : OmegaSpectrum.{u})

/-- 源の twist を経る比較と元の比較は、全 Hom の射影後に厳密に同じ射。 -/
lemma signedLoopSourceComparison_post_projection :
    RawSpectrumMapping.pointedPost Z
      (sequenceHom (signedLoopSourceTwistComparison X ≫ signedLoopSourceComparison X)) ≫
        RawSpectrumMapping.pointedPost Z (signedLoopProjection X) =
    RawSpectrumMapping.pointedPost Z (sequenceHom (signedLoopComparison X)) ≫
      RawSpectrumMapping.pointedPost Z (signedLoopProjection X) := by
  apply RawSpectrumMapping.pointed_hom_ext Z (KanSequence.signedLoopTail X.toKanSequence)
  intro n
  simp only [Category.assoc, RawSpectrumMapping.pointedPost_evaluation,
    RawSpectrumMapping.pointedPost_evaluation_assoc]
  change RawSpectrumMapping.pointedEvaluation Z
      (tail (cotensor CirclePower.space.{u} X)).toKanSequence n ≫
      (ihom (Z.level n).space).map
        ((signedLoopSourceTwistComparison X ≫ signedLoopSourceComparison X).app n) ≫
      (ihom (Z.level n).space).map ((signedLoopProjection X).app n) =
    RawSpectrumMapping.pointedEvaluation Z
      (tail (cotensor CirclePower.space.{u} X)).toKanSequence n ≫
      (ihom (Z.level n).space).map ((signedLoopComparison X).app n) ≫
      (ihom (Z.level n).space).map ((signedLoopProjection X).app n)
  rw [← Functor.map_comp, ← Functor.map_comp,
    signedLoopSourceComparison_factor, signedLoopComparison_projection]

/-- 元の同じ全 Hom で二つの BF 比較を結ぶ、射影が全区間で一定の実区間。 -/
def signedLoopSourceComparison_post_interval :
    PointedMapping.VerticalPath (RawSpectrumMapping.pointedPost Z (signedLoopProjection X))
      (RawSpectrumMapping.pointedPost Z
        (sequenceHom (signedLoopSourceTwistComparison X ≫ signedLoopSourceComparison X)))
      (RawSpectrumMapping.pointedPost Z (sequenceHom (signedLoopComparison X))) :=
  PointedMapping.verticalPathOfRlp _
    (RawSpectrumMapping.pointedPost_rlp Z (signedLoopProjection X)
      (fun n => (KanSequence.replacementStage
        (KanSequence.signedLoopTail X.toKanSequence) n).projection_rlp))
    _ _ (signedLoopSourceComparison_post_projection Z X)

end SerrePositivity.KST.Spectra.OmegaSpectrum
