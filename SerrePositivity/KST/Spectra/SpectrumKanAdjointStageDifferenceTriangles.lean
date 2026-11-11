module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointStrictStageSquares
public import SerrePositivity.KST.Spectra.PointedBasedPathDifference

/-!
概要：相対厳密化と単位後合成の段ごとの比較区間を、元の二辺と同じ実三角形で選ぶ。
方針：外ホーン充填の三角形を次段の源制限と前段の構造像へ移す。
規約：六つの面を実区間全体で保持。使われ方：共有辺を持つ構造正方形の相対比較。
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

/-- 元の共通始点からの二つの段区間を保つ、厳密な終点の比較区間と実三角形。 -/
def kanAdjointStageDifference (n : ℕ) :=
  PointedMapping.BasedPathDifference.choose
    (kanAdjointRelativeTracedStrictStageInterval X Y φ j n)
    (kanAdjointTracedUnitStageInterval X Y φ n)

/-- 次段の同じ比較三角形を、元の源の構造射へ制限した二単体。 -/
def kanAdjointStageDifferenceSourceTriangle (n : ℕ) :=
  SSet.yonedaEquiv.symm (kanAdjointStageDifference X Y φ j (n + 1)).triangle.simplex ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
      ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).level
        (n + 1)).space).right

/-- 前段の同じ比較三角形を、懸垂・標的構造射で移した二単体。 -/
def kanAdjointStageDifferenceTargetTriangle (n : ℕ) :=
  SSet.yonedaEquiv.symm (kanAdjointStageDifference X Y φ j n).triangle.simplex ≫
    (pointedStep X (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)) n).right

/-- 次段三角形の第一辺は、元の相対段区間の源制限。 -/
lemma kanAdjointStageDifferenceSourceTriangle_two (n : ℕ) :
    stdSimplex.δ (2 : Fin 3) ≫ kanAdjointStageDifferenceSourceTriangle X Y φ j n =
      ((kanAdjointRelativeTracedStrictStageInterval X Y φ j (n + 1)).pre (X.sigma n)).path := by
  rw [kanAdjointStageDifferenceSourceTriangle, ← Category.assoc,
    PointedMapping.BasedPathDifference.triangle_two]
  rfl

/-- 次段三角形の対角辺は、元の単位段区間の源制限。 -/
lemma kanAdjointStageDifferenceSourceTriangle_one (n : ℕ) :
    stdSimplex.δ (1 : Fin 3) ≫ kanAdjointStageDifferenceSourceTriangle X Y φ j n =
      ((kanAdjointTracedUnitStageInterval X Y φ (n + 1)).pre (X.sigma n)).path := by
  rw [kanAdjointStageDifferenceSourceTriangle, ← Category.assoc,
    PointedMapping.BasedPathDifference.triangle_one]
  rfl

/-- 次段三角形の第二辺は、同じ厳密終点比較区間の源制限。 -/
lemma kanAdjointStageDifferenceSourceTriangle_zero (n : ℕ) :
    stdSimplex.δ (0 : Fin 3) ≫ kanAdjointStageDifferenceSourceTriangle X Y φ j n =
      (((kanAdjointStageDifference X Y φ j (n + 1)).path).pre (X.sigma n)).path := by
  rw [kanAdjointStageDifferenceSourceTriangle, ← Category.assoc,
    PointedMapping.BasedPathDifference.triangle_zero]
  rfl

/-- 前段三角形の第一辺は、元の相対段区間の構造像。 -/
lemma kanAdjointStageDifferenceTargetTriangle_two (n : ℕ) :
    stdSimplex.δ (2 : Fin 3) ≫ kanAdjointStageDifferenceTargetTriangle X Y φ j n =
      ((PointedMapping.VerticalPath.basedPost
        (kanAdjointRelativeTracedStrictStageInterval X Y φ j n).suspension.forgetProjection
        ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path) := by
  rw [kanAdjointStageDifferenceTargetTriangle, ← Category.assoc,
    PointedMapping.BasedPathDifference.triangle_two,
    PointedMapping.VerticalPath.suspension_basedPost_path]
  rfl

/-- 前段三角形の対角辺は、元の単位段区間の構造像。 -/
lemma kanAdjointStageDifferenceTargetTriangle_one (n : ℕ) :
    stdSimplex.δ (1 : Fin 3) ≫ kanAdjointStageDifferenceTargetTriangle X Y φ j n =
      ((PointedMapping.VerticalPath.basedPost
        (kanAdjointTracedUnitStageInterval X Y φ n).suspension.forgetProjection
        ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path) := by
  rw [kanAdjointStageDifferenceTargetTriangle, ← Category.assoc,
    PointedMapping.BasedPathDifference.triangle_one,
    PointedMapping.VerticalPath.suspension_basedPost_path]
  rfl

/-- 前段三角形の第二辺は、同じ厳密終点比較区間の構造像。 -/
lemma kanAdjointStageDifferenceTargetTriangle_zero (n : ℕ) :
    stdSimplex.δ (0 : Fin 3) ≫ kanAdjointStageDifferenceTargetTriangle X Y φ j n =
      ((PointedMapping.VerticalPath.basedPost
        (kanAdjointStageDifference X Y φ j n).path.suspension.forgetProjection
        ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path) := by
  rw [kanAdjointStageDifferenceTargetTriangle, ← Category.assoc,
    PointedMapping.BasedPathDifference.triangle_zero,
    PointedMapping.VerticalPath.suspension_basedPost_path]
  rfl

end SerrePositivity.KST.Spectra.RawSpectrumMapping
