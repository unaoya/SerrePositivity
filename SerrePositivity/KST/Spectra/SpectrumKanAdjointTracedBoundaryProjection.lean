module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedBoundaryData
public import SerrePositivity.KST.Spectra.PointedTransposeIntervalRestriction

/-!
概要：具体的に選んだ非零境界の段調整を転置し、境界の帰納構成の同じ段射・区間へ戻す。
方針：指定区間の厳密な制限を交換同型で転置し、境界比較の二度の転置を消す。
規約：成分だけの比較に弱めない。使われ方：境界構造三角形との三辺の同定。
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

/-- 部分対象上の同じ帰納構成で得た比較を再び転置すると、保存した元の段比較へ戻る。 -/
lemma kanAdjointTracedBoundaryInterval_transpose_path (n : ℕ) :
    (kanAdjointTracedBoundaryInterval X Y φ j n).basedTranspose.path =
      (kanAdjointTracedStageComparison X Y (j ≫ φ) n).path := by
  have hp : (kanAdjointTracedBoundaryInterval X Y φ j n).path =
      (kanAdjointTracedStageComparison X Y (j ≫ φ) n).basedTranspose.path := by
    change (kanAdjointTracedEvaluationInterval X Y (j ≫ φ) n).path = _
    exact kanAdjointTracedEvaluationInterval_path X Y (j ≫ φ) n
  change (kanAdjointTracedBoundaryInterval X Y φ j n).path ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso B (X.level n).space
      ((KanSequence.signedLoopTail Y.toKanSequence).level n).space).hom.right = _
  rw [hp]
  exact (kanAdjointTracedStageComparison X Y (j ≫ φ) n).basedTranspose_twice_path

/-- 非零境界へ調整した座標の同じ比較区間を、cotensor 値の段射へ転置する。 -/
def kanAdjointTracedAdjustedStageInterval [Mono j.right] (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint
      ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).level n).space)
      (kanAdjointParameterStage X Y φ n)
      (kanAdjointTracedBoundaryCoordinate X Y φ j n).stage :=
  (kanAdjointTracedBoundaryCoordinate X Y φ j n).interval.basedTranspose

/-- 調整済み段射の射影は、元の部分対象の帰納構成の同じ段射に厳密に一致する。 -/
lemma kanAdjointTracedBoundaryCoordinate_stage_projection [Mono j.right] (n : ℕ) :
    (kanAdjointTracedBoundaryCoordinate X Y φ j n).stage ≫
      (KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app n =
        (kanAdjointTracedParameterHom X Y (j ≫ φ)).app n := by
  let s := kanAdjointTracedBoundaryCoordinate X Y φ j n
  have ht := PointedMapping.transpose_pre_outer s.coordinate j
  have hb := congrArg PointedMapping.transpose s.boundary
  have he := congrArg PointedMapping.transpose
    (parameterFamily_evaluation X (KanSequence.signedLoopTail Y.toKanSequence) B
      (kanAdjointTracedParameterHom X Y (j ≫ φ)) n)
  rw [PointedMapping.transpose_transpose] at he
  exact ht.symm.trans (hb.trans he)

/-- 調整済み段比較の区間全体も、元の境界の帰納構成の比較区間へ厳密に射影される。 -/
lemma kanAdjointTracedAdjustedStageInterval_projection_path [Mono j.right] (n : ℕ) :
    (kanAdjointTracedAdjustedStageInterval X Y φ j n).path ≫
      (PointedObject.basedHomMap (X.level n).space
        ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app n)).right =
      (kanAdjointTracedStageComparison X Y (j ≫ φ) n).path := by
  let s := kanAdjointTracedBoundaryCoordinate X Y φ j n
  let R := kanAdjointTracedBoundaryInterval X Y φ j n
  have hr : s.interval.path ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j (kanAdjointParameterTarget X Y n)).right = R.path := by
    apply PointedMapping.VerticalPath.path_restriction_eq_of_homotopy
    rw [KanAdjointBoundaryCoordinate.interval_h]
    exact s.comparison_boundary
  have h := PointedMapping.VerticalPath.basedTranspose_restriction_path s.interval R j hr
  rw [kanAdjointTracedBoundaryInterval_transpose_path] at h
  exact h

/-- 評価した段比較のホモトピーも、元の境界比較の同じ全区間へ射影される。 -/
lemma kanAdjointTracedAdjustedStageInterval_projection_h [Mono j.right] (n : ℕ) :
    (kanAdjointTracedAdjustedStageInterval X Y φ j n).homotopy.h ≫
      ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app n).right =
      (kanAdjointTracedStageComparison X Y (j ≫ φ) n).homotopy.h := by
  have h := congrArg (fun F ↦ uncurry (F ≫ PointedObject.basedHomι (X.level n).space
    ((KanSequence.mapping B (KanSequence.signedLoopTail Y.toKanSequence)).level n).space))
      (kanAdjointTracedAdjustedStageInterval_projection_path X Y φ j n)
  rw [Category.assoc, PointedObject.basedHomMap_ι, ← Category.assoc,
    uncurry_natural_right, ← PointedMapping.VerticalPath.homotopy_h,
    ← PointedMapping.VerticalPath.homotopy_h] at h
  exact h

end SerrePositivity.KST.Spectra.RawSpectrumMapping
