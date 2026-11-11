module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedUnitStep
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedUnitSquareBoundary

/-!
概要：保持した単位正方形を、前後の実評価区間の構造比較として表示する。
方針：第二辺の厳密同定で同じ正方形の終辺の型だけを照合する。
規約：正方形も境界も選び直さない。使われ方：共有する非定数辺での相対貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 同じ正方形は、次段評価の制限と前段評価の構造像の実ホモトピーを与える。 -/
def kanAdjointTracedUnitEvaluationSquare (n : ℕ) :
    SSet.Homotopy
      (((kanAdjointTracedUnitEvaluationInterval X Y φ (n + 1)).basedPost
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
          ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).path)
      (((kanAdjointTracedUnitEvaluationInterval X Y φ n).basedPost
        (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).path) where
  h := (kanAdjointTracedUnitParameterSquare X Y φ n).h
  h₀ := (kanAdjointTracedUnitParameterSquare X Y φ n).h₀
  h₁ := by
    rw [(kanAdjointTracedUnitParameterSquare X Y φ n).h₁]
    exact (kanAdjointTracedUnitParameterTriangle_zero X Y φ n).symm.trans
      (kanAdjointTracedUnitParameterTriangle_zero_evaluation X Y φ n)
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 評価区間表示へ移しても、同じ元の非定数構造辺を厳密に保持する。 -/
lemma kanAdjointTracedUnitEvaluationSquare_start (n : ℕ) :
    SquareAdjustment.leftSide ≫ (kanAdjointTracedUnitEvaluationSquare X Y φ n).h =
      (kanAdjointParameterStructureInterval X Y φ n).path :=
  kanAdjointTracedUnitParameterSquare_start X Y φ n

end SerrePositivity.KST.Spectra.RawSpectrumMapping
