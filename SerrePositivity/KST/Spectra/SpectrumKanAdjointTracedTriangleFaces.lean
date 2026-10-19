module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedStageTriangles

/-!
概要：正方形の上下に指定した同じ二単体の三辺を、元の段区間の制限と構造像へ照合する。
方針：元の段三角形の面の式に、同じ前合成と懸垂・後合成を施す。
規約：実区間と二単体を変更しない。使われ方：指定三角形を保つ段間正方形の充填。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right]

/-- 下側三角形の第一辺は、元の次段調整区間の同じ制限。 -/
lemma kanAdjointRelativeTracedSourceTriangle_two (n : ℕ) :
    stdSimplex.δ (2 : Fin 3) ≫ kanAdjointRelativeTracedSourceTriangle X Y φ j n =
      ((kanAdjointTracedAdjustedStageInterval X Y φ j (n + 1)).pre (X.sigma n)).path := by
  rw [kanAdjointRelativeTracedSourceTriangle, ← Category.assoc,
    kanAdjointRelativeTracedStageTriangle_two]
  rfl

/-- 下側三角形の第二辺は、同じ次段修正区間の制限。 -/
lemma kanAdjointRelativeTracedSourceTriangle_zero (n : ℕ) :
    stdSimplex.δ (0 : Fin 3) ≫ kanAdjointRelativeTracedSourceTriangle X Y φ j n =
      ((kanAdjointRelativeTracedStageCorrectionInterval X Y φ j (n + 1)).pre (X.sigma n)).path := by
  rw [kanAdjointRelativeTracedSourceTriangle, ← Category.assoc,
    kanAdjointRelativeTracedStageTriangle_zero]
  rfl

/-- 下側三角形の対角辺も、元の名前つき段区間の制限そのもの。 -/
lemma kanAdjointRelativeTracedSourceTriangle_one (n : ℕ) :
    stdSimplex.δ (1 : Fin 3) ≫ kanAdjointRelativeTracedSourceTriangle X Y φ j n =
      ((kanAdjointRelativeTracedStageEvaluationInterval X Y φ j (n + 1)).pre (X.sigma n)).path := by
  rw [kanAdjointRelativeTracedSourceTriangle, ← Category.assoc,
    kanAdjointRelativeTracedStageTriangle_one]
  rfl

/-- 上側三角形の第一辺は、元の前段調整区間の構造像。 -/
lemma kanAdjointRelativeTracedTargetTriangle_two (n : ℕ) :
    stdSimplex.δ (2 : Fin 3) ≫ kanAdjointRelativeTracedTargetTriangle X Y φ j n =
      ((kanAdjointTracedAdjustedStageInterval X Y φ j n).suspension.forgetProjection.basedPost
        ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path := by
  rw [kanAdjointRelativeTracedTargetTriangle, ← Category.assoc, ← Category.assoc,
    kanAdjointRelativeTracedStageTriangle_two]
  rfl

/-- 上側三角形の第二辺は、同じ前段修正区間の構造像。 -/
lemma kanAdjointRelativeTracedTargetTriangle_zero (n : ℕ) :
    stdSimplex.δ (0 : Fin 3) ≫ kanAdjointRelativeTracedTargetTriangle X Y φ j n =
      ((kanAdjointRelativeTracedStageCorrectionInterval
          X Y φ j n).suspension.forgetProjection.basedPost
        ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path := by
  rw [kanAdjointRelativeTracedTargetTriangle, ← Category.assoc, ← Category.assoc,
    kanAdjointRelativeTracedStageTriangle_zero]
  rfl

/-- 上側三角形の対角辺も、元の名前つき段区間の構造像そのもの。 -/
lemma kanAdjointRelativeTracedTargetTriangle_one (n : ℕ) :
    stdSimplex.δ (1 : Fin 3) ≫ kanAdjointRelativeTracedTargetTriangle X Y φ j n =
      ((kanAdjointRelativeTracedStageEvaluationInterval
          X Y φ j n).suspension.forgetProjection.basedPost
        ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path := by
  rw [kanAdjointRelativeTracedTargetTriangle, ← Category.assoc, ← Category.assoc,
    kanAdjointRelativeTracedStageTriangle_one]
  rfl

end SerrePositivity.KST.Spectra.RawSpectrumMapping
