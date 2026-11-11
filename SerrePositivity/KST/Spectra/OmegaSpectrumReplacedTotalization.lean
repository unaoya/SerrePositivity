module

public import SerrePositivity.KST.Spectra.ReplacedOrdinaryTotalization

/-!
概要：任意の余単体 Ω スペクトルの Reedy 置換した通常 Tot と既存 homotopyTotalization。
方針：Kan 列としての置換と比較を元の BF 図式に適用する。
規約：元の図式への Reedy 仮定は不要。選択した比較は全整数次数で π 同型。
使われ方：Goerss–Jardine VIII §1、BF 1978 §2。Sp-4 の公開界面。
-/

@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 任意の余単体 BF 図式の、Reedy 置換した通常 Tot の BF 模型。 -/
def replacedOrdinaryTotalization (X : CosimplicialObject OmegaSpectrum.{u}) :
    OmegaSpectrum.{u} :=
  CosimplicialSequenceReedyReplacement.totalization (X ⋙ forgetToKan)
    (fun j ↦ (X.obj j).toKanSequence_omega)

/-- Reedy 置換した通常 Tot から既存の homotopyTotalization への実際の BF 射。 -/
def replacedOrdinaryTotalizationComparison (X : CosimplicialObject OmegaSpectrum.{u}) :
    replacedOrdinaryTotalization X ⟶ homotopyTotalization X :=
  CosimplicialSequenceReedyReplacement.comparison (X ⋙ forgetToKan)
    (fun j ↦ (X.obj j).toKanSequence_omega)

/-- 比較は零次数を含む各段の全基点 π 同型。 -/
lemma replacedOrdinaryTotalizationComparison_levelwise
    (X : CosimplicialObject OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((replacedOrdinaryTotalizationComparison X).app n).right :=
  CosimplicialSequenceReedyReplacement.comparison_levelwise (X ⋙ forgetToKan)
    (fun j ↦ (X.obj j).toKanSequence_omega) n

/-- 比較は全整数次数のホモトピー群で同型。 -/
lemma replacedOrdinaryTotalizationComparison_piIsomorphism
    (X : CosimplicialObject OmegaSpectrum.{u}) :
    PiIsomorphism (replacedOrdinaryTotalizationComparison X) :=
  piIsomorphism_of_levelwise _ (replacedOrdinaryTotalizationComparison_levelwise X)

end
end SerrePositivity.KST.Spectra.OmegaSpectrum
