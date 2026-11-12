module

public import SerrePositivity.KST.Spectra.OrdinaryTotalizationSpectrumMap

/-!
概要：余単体 Ω スペクトルの通常 Tot の BF 模型から既存の homotopyTotalization への比較。
方針：段ごとの Reedy 条件を Kan 列へ渡し、構成した BF 比較を元のスペクトル図式に適用する。
規約：標的は既存の homotopyTotalization そのもの。∞ 極限性は別工程。
使われ方：Goerss–Jardine VIII §1、BF 1978 §2。Sp-4 の公開比較。
-/

@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : CosimplicialObject OmegaSpectrum.{u})
  (hX : KanSequence.TotalizationReedy (X ⋙ forgetToKan))

/-- Reedy 条件を満たす余単体スペクトルの通常 Tot の実際の BF 模型。 -/
def ordinaryTotalization : OmegaSpectrum.{u} :=
  KanSequence.totalizationSpectrum (X ⋙ forgetToKan) hX (fun j ↦ (X.obj j).toKanSequence_omega)

/-- 通常 Tot の BF 模型から既存の homotopyTotalization への実際の BF 射。 -/
def ordinaryTotalizationComparison : ordinaryTotalization X hX ⟶ homotopyTotalization X :=
  KanSequence.totalizationSpectrumMap (X ⋙ forgetToKan) hX
    (fun j ↦ (X.obj j).toKanSequence_omega)

/-- 通常 Tot の比較は各段で全基点 π 同型。 -/
lemma ordinaryTotalizationComparison_levelwise (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((ordinaryTotalizationComparison X hX).app n).right :=
  KanSequence.totalizationSpectrumMap_levelwise (X ⋙ forgetToKan) hX
    (fun j ↦ (X.obj j).toKanSequence_omega) n

/-- 既存の homotopy Tot への標準比較は全整数次数のホモトピー群で同型。 -/
lemma ordinaryTotalizationComparison_piIsomorphism :
    PiIsomorphism (ordinaryTotalizationComparison X hX) :=
  piIsomorphism_of_levelwise _ (ordinaryTotalizationComparison_levelwise X hX)

end
end SerrePositivity.KST.Spectra.OmegaSpectrum
