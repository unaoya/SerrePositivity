module

public import SerrePositivity.KST.Spectra.PointedMappedIntervalTransposeStep
public import SerrePositivity.KST.Spectra.SpectrumTracedSourceUnitStageCoordinates
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedUnitStep

/-!
概要：源単位の同じ構造三角形の第二辺を、前段の実評価区間の構造像へ同定する。
方針：同じパラメータ付き列射の構造条件と、構造像・転置の交換を使う。
規約：指定辺を保持し、充填を選び直さない。使われ方：源単位側の実構造正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 源単位の同じ第二辺は、前段のパラメータ付き実区間の構造像そのもの。 -/
lemma tracedSourceUnitParameterTriangle_zero_stage (n : ℕ) :
    stdSimplex.δ (0 : Fin 3) ≫ tracedSourceUnitParameterTriangle X Y φ n =
      ((tracedSourceUnitStageInterval X Y φ n).basedPost
        (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).path := by
  rw [tracedSourceUnitParameterTriangle_zero,
    PointedMapping.VerticalPath.basedPreAction_action_path]
  change (OmegaSpectrum.tracedSignedLoopUnitStepInterval X n).path ≫
    (tracedSourceUnitStructureAction X Y φ n).right = _
  rw [tracedSourceUnitStructureAction_post, OmegaSpectrum.tracedSignedLoopUnitStepInterval_path]
  let H := OmegaSpectrum.tracedSignedLoopUnitComparison X n
  let p := KanSequence.signedLoopParameterHom
    (homOfParameterFamily X Y.toKanSequence A φ)
  have hs := PointedMapping.VerticalPath.basedPost_sequence_step_path p n H
  have ht := congrArg (· ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) A
    ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom.right) hs.symm
  change ((H.suspension.forgetProjection.basedPost
    ((KanSequence.signedLoopTail X.toKanSequence).sigma n)).basedPost
      (p.app (n + 1))).basedTranspose.path = _ at ht
  change ((H.suspension.forgetProjection.basedPost
    ((KanSequence.signedLoopTail X.toKanSequence).sigma n)).basedPost
      (p.app (n + 1))).basedTranspose.path = _
  exact ht.trans (basedTranspose_mapped_step_path X (KanSequence.signedLoopTail Y.toKanSequence)
    n (H.basedPost (p.app n)))

/-- 第二辺も、元の源単位評価区間の前段の構造像と辺全体で一致する。 -/
lemma tracedSourceUnitParameterTriangle_zero_evaluation (n : ℕ) :
    stdSimplex.δ (0 : Fin 3) ≫ tracedSourceUnitParameterTriangle X Y φ n =
      (((OmegaSpectrum.CotensorCompatible.kanAdjointTracedSourceEvaluationInterval
        X Y n).pre φ).basedPost
          (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).path := by
  rw [tracedSourceUnitParameterTriangle_zero_stage]
  change (tracedSourceUnitStageInterval X Y φ n).path ≫ _ = _
  rw [tracedSourceUnitStageInterval_path]
  rfl

end SerrePositivity.KST.Spectra.RawSpectrumMapping
