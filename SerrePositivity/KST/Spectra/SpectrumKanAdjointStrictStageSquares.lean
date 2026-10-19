module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointStrictStageIntervals

/-!
概要：厳密な二つの終点を持つ段区間へ、元の二つの構造正方形を同じまま移す。
方針：前合成と懸垂・後合成で保持される実区間の式を使う。
規約：正方形の全体を変更しない。使われ方：指定三角形上の共有辺比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right]

/-- 厳密な相対列射を終点とする段区間の、同じ構造正方形。 -/
def kanAdjointRelativeTracedStrictStageSquare (n : ℕ) :
    SSet.Homotopy
      ((kanAdjointRelativeTracedStrictStageInterval X Y φ j (n + 1)).pre (X.sigma n)).path
      ((PointedMapping.VerticalPath.basedPost
        (kanAdjointRelativeTracedStrictStageInterval X Y φ j n).suspension.forgetProjection
        ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path)
    where
  h := (kanAdjointRelativeTracedPastedSquare X Y φ j n).h
  h₀ := by
    change SSet.ι₀ ≫ (kanAdjointRelativeTracedPastedSquare X Y φ j n).h =
      (kanAdjointRelativeTracedStrictStageInterval X Y φ j (n + 1)).path ≫ _
    rw [kanAdjointRelativeTracedStrictStageInterval_path]
    exact (kanAdjointRelativeTracedEvaluationStructureHomotopy X Y φ j n).h₀
  h₁ := by
    rw [kanAdjointRelativeTracedStrictStageInterval_step_path]
    exact (kanAdjointRelativeTracedEvaluationStructureHomotopy X Y φ j n).h₁
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 厳密な単位後合成の列射を終点とする段区間の、同じ構造正方形。 -/
def kanAdjointTracedUnitStrictStageSquare (n : ℕ) :
    SSet.Homotopy
      ((kanAdjointTracedUnitStageInterval X Y φ (n + 1)).pre (X.sigma n)).path
      ((PointedMapping.VerticalPath.basedPost
        (kanAdjointTracedUnitStageInterval X Y φ n).suspension.forgetProjection
        ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path)
    where
  h := (kanAdjointTracedUnitStageSquare X Y φ n).h
  h₀ := by
    change SSet.ι₀ ≫ (kanAdjointTracedUnitStageSquare X Y φ n).h =
      (kanAdjointTracedUnitStageInterval X Y φ (n + 1)).path ≫ _
    rw [kanAdjointTracedUnitStageInterval_path]
    exact (kanAdjointTracedUnitStageSquare X Y φ n).h₀
  h₁ := by
    rw [kanAdjointTracedUnitStageInterval_step_path]
    exact (kanAdjointTracedUnitStageSquare X Y φ n).h₁
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

end SerrePositivity.KST.Spectra.RawSpectrumMapping
