module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedBoundaryProjection
public import SerrePositivity.KST.Spectra.PointedIntervalProjectionNaturality

/-!
概要：元の構造区間・次段修正の制限・前段修正の構造像の三辺を、境界の同じ区間へ射影する。
方針：普遍係数区間への入力の自然性と、転置済み段比較の厳密射影を使う。
規約：全区間の等式。使われ方：境界の帰納構造三角形と三辺輸送の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A)

/-- 元の懸垂評価の入力は、部分パラメータへの前合成と厳密に可換。 -/
lemma kanAdjointStructureInput_restriction (n : ℕ) :
    j ≫ kanAdjointStructureInput X Y φ n = kanAdjointStructureInput X Y (j ≫ φ) n := by
  simp only [kanAdjointStructureInput, Category.assoc]

/-- 元の普遍係数構造区間の制限は、部分対象の入力で作る同じ構造区間。 -/
lemma kanAdjointParameterStructureInterval_restriction_path (n : ℕ) :
    (kanAdjointParameterStructureInterval X Y φ n).path ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).right =
      (kanAdjointParameterStructureInterval X Y (j ≫ φ) n).path := by
  apply PointedMapping.VerticalPath.path_restriction_eq_of_homotopy
  rw [kanAdjointParameterStructureInterval_boundary, kanAdjointParameterStructureInterval_h,
    kanAdjointStructureInput_restriction]

/-- 元の構造区間の同じ転置も、境界の帰納構成の同じ構造区間へ射影される。 -/
lemma kanAdjointTracedStructureInterval_projection_path (n : ℕ) :
    (kanAdjointTracedStructureInterval X Y φ n).path ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app
          (n + 1))).right =
      (kanAdjointTracedStructureInterval X Y (j ≫ φ) n).path := by
  have h := PointedMapping.VerticalPath.basedTranspose_restriction_path
    (kanAdjointParameterStructureInterval X Y φ n)
    (kanAdjointParameterStructureInterval X Y (j ≫ φ) n) j
    (kanAdjointParameterStructureInterval_restriction_path X Y φ j n)
  change (kanAdjointParameterStructureInterval X Y φ n).basedTranspose.path ≫
    (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
      ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app
        (n + 1))).right =
    (kanAdjointParameterStructureInterval X Y (j ≫ φ) n).basedTranspose.path
  exact h

/-- 次段修正の構造射への制限は、境界の次段修正を制限した同じ区間へ射影される。 -/
lemma kanAdjointTracedNextCorrection_projection_path [Mono j.right] (n : ℕ) :
    ((kanAdjointTracedAdjustedStageInterval X Y φ j (n + 1)).pre (X.sigma n)).path ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app
          (n + 1))).right =
      ((kanAdjointTracedStageComparison X Y (j ≫ φ) (n + 1)).pre (X.sigma n)).path :=
  PointedMapping.VerticalPath.pre_projection_path _ _ _
    (kanAdjointTracedAdjustedStageInterval_projection_path X Y φ j (n + 1)) (X.sigma n)

/-- 前段修正の構造像も、境界の前段修正の同じ構造像へ全区間で射影される。 -/
lemma kanAdjointTracedPreviousCorrection_projection_path [Mono j.right] (n : ℕ) :
    ((kanAdjointTracedAdjustedStageInterval X Y φ j n).suspension.forgetProjection.basedPost
      ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path ≫
      (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app
          (n + 1))).right =
      ((kanAdjointTracedStageComparison X Y (j ≫ φ) n).suspension.forgetProjection.basedPost
        ((KanSequence.mapping B (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path := by
  let P := kanAdjointTracedAdjustedStageInterval X Y φ j n
  let Q := kanAdjointTracedStageComparison X Y (j ≫ φ) n
  let q := KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)
  have hs := P.suspension_projection_path Q (q.app n)
    (kanAdjointTracedAdjustedStageInterval_projection_path X Y φ j n)
  exact PointedMapping.VerticalPath.post_projection_path _ _ _ hs (q.app (n + 1))
    ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)
    ((KanSequence.mapping B (KanSequence.signedLoopTail Y.toKanSequence)).sigma n) (q.comm n).symm

end SerrePositivity.KST.Spectra.RawSpectrumMapping
