module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedEvaluationComposite

/-!
概要：名前つきで選んだ同じ段評価の合成三角形を、元の cotensor 値の段射へ転置する。
方針：同じ二単体に内部 Hom の交換射を後合成し、三辺を元の区間族へ厳密に照合する。
規約：二単体を選び直さない。使われ方：段間正方形の上下に指定する同じ三角形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right]

/-- 元の段座標の合成区間を、同じ cotensor 値の段区間へ転置する。 -/
def kanAdjointRelativeTracedStageEvaluationInterval (n : ℕ) :=
  (kanAdjointRelativeTracedEvaluationInterval X Y φ j n).basedTranspose

/-- 保持した相対修正区間を、同じ cotensor 値の段区間へ戻す。 -/
def kanAdjointRelativeTracedStageCorrectionInterval (n : ℕ) :=
  (kanAdjointRelativeTracedCorrectionInterval X Y φ j n).val.basedTranspose

/-- 転置して戻した修正区間は、相対帰納構成で保持した同じ実垂直区間を持つ。 -/
lemma kanAdjointRelativeTracedStageCorrectionInterval_path (n : ℕ) :
    (kanAdjointRelativeTracedStageCorrectionInterval X Y φ j n).path =
      (relativeTracedParameterComparison X (KanSequence.signedLoopTail Y.toKanSequence) j
        (kanAdjointTracedBoundary X Y φ j)
        (fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).stage)
        (fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).projection)
        (kanAdjointCanonicalVerticalStructurePath X Y φ j) n).path := by
  let Q := relativeTracedParameterEvaluationInterval X
    (KanSequence.signedLoopTail Y.toKanSequence) j (kanAdjointTracedBoundary X Y φ j)
    (fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).stage)
    (fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).projection)
    (kanAdjointCanonicalVerticalStructurePath X Y φ j) n
  have he : (kanAdjointRelativeTracedStageCorrectionInterval X Y φ j n).path =
      Q.val.basedTranspose.path :=
    PointedMapping.VerticalPath.changeEndpoints_basedTranspose_path Q.val
      (PointedMapping.transpose_transpose
        (kanAdjointTracedBoundaryCoordinate X Y φ j n).coordinate).symm rfl
  exact he.trans (relativeTracedParameterEvaluationInterval_transpose_path X
    (KanSequence.signedLoopTail Y.toKanSequence) j (kanAdjointTracedBoundary X Y φ j)
    (fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).stage)
    (fun n ↦ (kanAdjointTracedBoundaryCoordinate X Y φ j n).projection)
    (kanAdjointCanonicalVerticalStructurePath X Y φ j) n)

/-- 段評価の同じ二単体を、内部 Hom の交換射だけで段射の三角形へ戻す。 -/
def kanAdjointRelativeTracedStageTriangle (n : ℕ) :=
  kanAdjointRelativeTracedEvaluationTriangle X Y φ j n ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A (X.level n).space
      ((KanSequence.signedLoopTail Y.toKanSequence).level n).space).hom.right

/-- 第一辺は、同じ元の段調整区間。 -/
lemma kanAdjointRelativeTracedStageTriangle_two (n : ℕ) :
    stdSimplex.δ (2 : Fin 3) ≫ kanAdjointRelativeTracedStageTriangle X Y φ j n =
      (kanAdjointTracedAdjustedStageInterval X Y φ j n).path := by
  rw [kanAdjointRelativeTracedStageTriangle, ← Category.assoc,
    kanAdjointRelativeTracedEvaluationTriangle_two]
  rfl

/-- 第二辺も、同じ元の相対修正区間。 -/
lemma kanAdjointRelativeTracedStageTriangle_zero (n : ℕ) :
    stdSimplex.δ (0 : Fin 3) ≫ kanAdjointRelativeTracedStageTriangle X Y φ j n =
      (kanAdjointRelativeTracedStageCorrectionInterval X Y φ j n).path := by
  rw [kanAdjointRelativeTracedStageTriangle, ← Category.assoc,
    kanAdjointRelativeTracedEvaluationTriangle_zero]
  rfl

/-- 対角辺は、名前つきで選んだ同じ段区間の転置。 -/
lemma kanAdjointRelativeTracedStageTriangle_one (n : ℕ) :
    stdSimplex.δ (1 : Fin 3) ≫ kanAdjointRelativeTracedStageTriangle X Y φ j n =
      (kanAdjointRelativeTracedStageEvaluationInterval X Y φ j n).path := by
  rw [kanAdjointRelativeTracedStageTriangle, ← Category.assoc,
    kanAdjointRelativeTracedEvaluationTriangle_one]
  rfl

/-- 次段の同じ三角形を構造射へ制限した、正方形の下辺に指定する二単体。 -/
def kanAdjointRelativeTracedSourceTriangle (n : ℕ) :=
  kanAdjointRelativeTracedStageTriangle X Y φ j (n + 1) ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
      ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).level
        (n + 1)).space).right

/-- 前段の同じ三角形の懸垂と構造像を取った、正方形の上辺に指定する二単体。 -/
def kanAdjointRelativeTracedTargetTriangle (n : ℕ) :=
  kanAdjointRelativeTracedStageTriangle X Y φ j n ≫
    (suspensionHom (X.level n).space
      ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).level n).space).right ≫
    (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
      ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).right

end SerrePositivity.KST.Spectra.RawSpectrumMapping
