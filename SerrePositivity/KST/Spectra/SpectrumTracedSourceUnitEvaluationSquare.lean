module

public import SerrePositivity.KST.Spectra.SpectrumTracedSourceUnitStep
public import SerrePositivity.KST.Spectra.SpectrumTracedSourceUnitParameterSquare

/-!
概要：同じ源単位正方形を、元の前後の評価区間の実構造比較として表示する。
方針：保存済み対角辺と第二辺の厳密同定だけで端点表示をそろえる。
規約：非定数の構造入力と定数の終点境界を保持。使われ方：差の正方形の指定境界。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
open OmegaSpectrum.CotensorCompatible
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 元の次段評価区間の構造制限と、前段評価区間の構造像の同じ実正方形。 -/
def tracedSourceUnitEvaluationSquare (n : ℕ) :
    SSet.Homotopy
      ((((kanAdjointTracedSourceEvaluationInterval X Y (n + 1)).pre φ).basedPost
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n)
          ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)).path)
      ((((kanAdjointTracedSourceEvaluationInterval X Y n).pre φ).basedPost
        (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).path) where
  h := (tracedSourceUnitParameterSquare X Y φ n).h
  h₀ := (tracedSourceUnitParameterSquare X Y φ n).h₀.trans
    ((tracedSourceUnitParameterTriangle_one_stage X Y φ n).symm.trans
      (tracedSourceUnitParameterTriangle_one_evaluation X Y φ n))
  h₁ := (tracedSourceUnitParameterSquare X Y φ n).h₁.trans
    ((tracedSourceUnitParameterTriangle_zero X Y φ n).symm.trans
      (tracedSourceUnitParameterTriangle_zero_evaluation X Y φ n))
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 元の評価区間へ表示を変えても、同じ非定数の源構造辺全体を保持する。 -/
lemma tracedSourceUnitEvaluationSquare_start (n : ℕ) :
    SquareAdjustment.leftSide ≫ (tracedSourceUnitEvaluationSquare X Y φ n).h =
      ((OmegaSpectrum.signedLoopUnitStructurePath X n).basedPreAction
        (tracedSourceUnitStructureInput X Y φ n) (𝟙 A)).path :=
  tracedSourceUnitParameterSquare_start X Y φ n

/-- 終点境界も、元の厳密な源単位族の同じ構造頂点で全区間が一定。 -/
lemma tracedSourceUnitEvaluationSquare_finish (n : ℕ) :
    SquareAdjustment.rightSide ≫ (tracedSourceUnitEvaluationSquare X Y φ n).h =
      SSet.const (PointedMapping.familyVertex ((φ ≫ tracedSourceUnitAction X Y n) ≫
        pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)) := by
  change SquareAdjustment.rightSide ≫ (tracedSourceUnitParameterSquare X Y φ n).h = _
  rw [tracedSourceUnitParameterSquare_finish]
  have he := (tracedSourceUnitParameterTriangle_zero X Y φ n).symm.trans
    (tracedSourceUnitParameterTriangle_zero_evaluation X Y φ n)
  have hv := congrArg (fun F => SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ F)) he
  have hr := congrArg SSet.yonedaEquiv
    (((kanAdjointTracedSourceEvaluationInterval X Y n).pre φ).basedPost
      (pointedStep X (KanSequence.signedLoopTail Y.toKanSequence) n)).one
  exact congrArg SSet.const (hv.trans hr)

end SerrePositivity.KST.Spectra.RawSpectrumMapping
