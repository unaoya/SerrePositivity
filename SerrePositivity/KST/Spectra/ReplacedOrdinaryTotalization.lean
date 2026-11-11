module

public import SerrePositivity.KST.Spectra.CosimplicialSequenceReedyReplacement
public import SerrePositivity.KST.Spectra.OrdinaryTotalizationSpectrumMap
public import SerrePositivity.KST.Spectra.SpectrumLevelwiseInverse

/-!
概要：任意の余単体 Kan Ω 列の Reedy 置換した通常 Tot を、元の homotopy Tot と比較する。
方針：厳密な Ω 図式の置換単位の BK 比較を BF 射へ持ち上げ、その逆向きの射を合成する。
規約：実際の BF 射と全基点・全整数次数の π 同型を構成する。∞ 極限性は後続工程。
使われ方：Goerss–Jardine VII §4、VIII §1、BF 1978 §2。Sp-4 の任意の図式への合流。
-/

@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.CosimplicialSequenceReedyReplacement
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (D : CosimplicialObject KanSequence.{u}) (hD : ∀ j, (D.obj j).OmegaCondition)

/-- 置換した実際の列の図式は各段 Reedy Kan。 -/
lemma diagram_reedy : KanSequence.TotalizationReedy (diagram D) :=
  fun n ↦ level_reedyTerminal D n

/-- Reedy 置換した通常 Tot の実際の BF 模型。 -/
def totalization : OmegaSpectrum.{u} :=
  KanSequence.totalizationSpectrum (diagram D) (diagram_reedy D)
    (sequence_omegaCondition D hD)

/-- 元の図式の BK homotopy Tot の BF 模型。 -/
def originalHomotopyTotalization : OmegaSpectrum.{u} :=
  KanSequence.homotopyLimitSpectrum (AsSmall.down ⋙ D)
    (fun j ↦ hD (AsSmall.down.obj j))

/-- 置換後の BK homotopy Tot の BF 模型。 -/
def replacedHomotopyTotalization : OmegaSpectrum.{u} :=
  KanSequence.homotopyLimitSpectrum (AsSmall.down ⋙ diagram D)
    (fun j ↦ sequence_omegaCondition D hD (AsSmall.down.obj j))

/-- 置換単位が誘導する実際の BK の BF 射。 -/
def homotopyUnit : originalHomotopyTotalization D hD ⟶
    replacedHomotopyTotalization D hD :=
  KanSequence.homotopyLimitSpectrumMap _ _ (Functor.whiskerLeft AsSmall.down (unitApp D))

/-- BK の置換単位は各段で全基点 π 同型。 -/
lemma homotopyUnit_levelwise (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((homotopyUnit D hD).app n).right :=
  KanSequence.homotopyLimitSpectrumMap_levelwise _ _
    (Functor.whiskerLeft AsSmall.down (unitApp D))
    (fun j n ↦ unit_piIsomorphism D (AsSmall.down.obj j) n) n

/-- Reedy 置換した通常 Tot から元の homotopy Tot への実際の BF 比較。 -/
def comparison : totalization D hD ⟶ originalHomotopyTotalization D hD :=
  KanSequence.totalizationSpectrumMap (diagram D) (diagram_reedy D)
    (sequence_omegaCondition D hD) ≫
    OmegaSpectrum.levelwiseInverse (homotopyUnit D hD) (homotopyUnit_levelwise D hD)

/-- 任意の Ω 図式の比較は各段で全基点 π 同型。 -/
lemma comparison_levelwise (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((comparison D hD).app n).right :=
  (KanSequence.totalizationSpectrumMap_levelwise (diagram D) (diagram_reedy D)
    (sequence_omegaCondition D hD) n).comp
    (OmegaSpectrum.levelwiseInverse_levelwise (homotopyUnit D hD)
      (homotopyUnit_levelwise D hD) n)

/-- Reedy 置換した通常 Tot と元の homotopy Tot の全整数次数の比較。 -/
lemma comparison_piIsomorphism : OmegaSpectrum.PiIsomorphism (comparison D hD) :=
  OmegaSpectrum.piIsomorphism_of_levelwise _ (comparison_levelwise D hD)

end
end SerrePositivity.KST.Spectra.CosimplicialSequenceReedyReplacement
