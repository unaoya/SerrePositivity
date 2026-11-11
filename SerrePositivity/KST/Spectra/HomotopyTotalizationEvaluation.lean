module

public import SerrePositivity.KST.Spectra.StableTotalizationConvergence
public import SerrePositivity.KST.Spectra.OmegaSpectrumReplacedTotalization

/-!
概要：既存 homotopyTotalization の整数次数の群を Reedy 置換した通常 Tot の段へ移す。
方針：実際の BF 比較射が誘導する群同型の逆と、通常 Tot の段評価を合成する。
規約：元の Ω 図式の Reedy 条件は要求しない。選択した比較に沿う同型。
使われ方：Goerss–Jardine VIII §1、BF 1978 §2。既存 homotopy Tot の Milnor 界面。
-/

@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.HomotopyTotalizationMilnor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 元の BF 図式を忘却して Reedy 置換した厳密な Kan Ω 列の図式。 -/
abbrev diagram (X : CosimplicialObject OmegaSpectrum.{u}) :=
  CosimplicialSequenceReedyReplacement.diagram (X ⋙ OmegaSpectrum.forgetToKan)

/-- 置換図式の段ごとの実際の Reedy Kan 条件。 -/
lemma reedy (X : CosimplicialObject OmegaSpectrum.{u}) :
    KanSequence.TotalizationReedy (diagram X) :=
  CosimplicialSequenceReedyReplacement.diagram_reedy _

/-- 置換図式の各対象の Ω 条件。 -/
lemma omegaCondition (X : CosimplicialObject OmegaSpectrum.{u}) :
    ∀ a, ((diagram X).obj a).OmegaCondition :=
  CosimplicialSequenceReedyReplacement.sequence_omegaCondition _
    (fun a ↦ (X.obj a).toKanSequence_omega)

/-- 比較の逆に沿って、元の homotopy Tot の整数次数を通常 Tot の指定段で計算する。 -/
def evaluation (X : CosimplicialObject OmegaSpectrum.{u})
    (j : ℤ) (k r : ℕ) (hk : j + (k : ℤ) = (r + 1 : ℕ)) :
    letI := PointedTotalization.kanComplex (diagram X ⋙ KanSequence.levelEvaluation k)
      ((CosimplicialHornFibration.terminal_iff _).mp (reedy X k))
    OmegaSpectrum.homotopyGroup (homotopyTotalization X) j ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedTotalization.obj (diagram X ⋙ KanSequence.levelEvaluation k)).right r
        (PointedTotalization.obj (diagram X ⋙ KanSequence.levelEvaluation k)).basepoint := by
  let := PointedTotalization.kanComplex (diagram X ⋙ KanSequence.levelEvaluation k)
    ((CosimplicialHornFibration.terminal_iff _).mp (reedy X k))
  exact (OmegaSpectrum.replacedOrdinaryTotalizationComparison_piIsomorphism X).groupEquiv j |>.symm
    |>.trans (TotalizationMilnor.evaluation (diagram X) (reedy X) (omegaCondition X) j k r hk)

end
end SerrePositivity.KST.Spectra.HomotopyTotalizationMilnor
