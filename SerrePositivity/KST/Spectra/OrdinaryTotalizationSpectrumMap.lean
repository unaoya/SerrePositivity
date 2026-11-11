module

public import SerrePositivity.KST.Spectra.OrdinaryTotalizationSpectrum
public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitMap

/-!
概要：通常 Tot の BF 模型から homotopy Tot の BF 模型への実際の全整数次数 π 同型。
方針：単射構造射を持つ源から標的の全単射 RLP 射影へ列の比較を持ち上げる。
規約：射影との厳密な可換式と各段の全基点 π 同型を証明する。
使われ方：BF 1978 §2、Goerss–Jardine VIII §1。Sp-4 の BF 模型どうしの比較。
-/

@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.KanSequence
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable (D : CosimplicialObject KanSequence.{u}) (hD : TotalizationReedy D)
  (hΩ : ∀ j, (D.obj j).OmegaCondition)

/-- 通常 Tot の BF 模型から homotopy Tot の BF 模型への実際の射。 -/
def totalizationSpectrumMap : totalizationSpectrum D hD hΩ ⟶
    homotopyLimitSpectrum (AsSmall.down ⋙ D) (fun j ↦ hΩ (AsSmall.down.obj j)) := by
  let f := liftHom (X := (totalizationSpectrum D hD hΩ).toKanSequence)
    (W := (homotopyLimitSpectrum (AsSmall.down ⋙ D)
      (fun j ↦ hΩ (AsSmall.down.obj j))).toKanSequence)
    (Z := homotopyLimit (AsSmall.down ⋙ D))
    (totalizationSpectrum D hD hΩ).sigma_mono (homotopyTotalizationComparison D hΩ)
    (fun n ↦ (replacementStage (homotopyLimit (AsSmall.down ⋙ D)) n).projection_rlp)
    (totalizationSpectrumComparison D hD hΩ)
  exact { app := f.app, comm := f.comm }

/-- BF 射を共通の end へ射影すると構成済みの通常 Tot 比較に戻る。 -/
lemma totalizationSpectrumMap_projection (n : ℕ) :
    (totalizationSpectrumMap D hD hΩ).app n ≫
      (homotopyTotalizationComparison D hΩ).app n =
    (totalizationSpectrumComparison D hD hΩ).app n :=
  liftHom_fac (X := (totalizationSpectrum D hD hΩ).toKanSequence)
    (W := (homotopyLimitSpectrum (AsSmall.down ⋙ D)
      (fun j ↦ hΩ (AsSmall.down.obj j))).toKanSequence)
    (Z := homotopyLimit (AsSmall.down ⋙ D))
    (totalizationSpectrum D hD hΩ).sigma_mono (homotopyTotalizationComparison D hΩ)
    (fun k ↦ (replacementStage (homotopyLimit (AsSmall.down ⋙ D)) k).projection_rlp)
    (totalizationSpectrumComparison D hD hΩ) n

/-- 実際の BF 比較射は各段で全基点 π 同型。 -/
lemma totalizationSpectrumMap_levelwise (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((totalizationSpectrumMap D hD hΩ).app n).right := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp
    (g := ((homotopyTotalizationComparison D hΩ).app n).right) _
    (homotopyTotalizationComparison_levelwise D hΩ n)
  have he := congrArg Under.Hom.right (totalizationSpectrumMap_projection D hD hΩ n)
  change ((totalizationSpectrumMap D hD hΩ).app n).right ≫
    ((homotopyTotalizationComparison D hΩ).app n).right =
    ((totalizationSpectrumComparison D hD hΩ).app n).right at he
  rw [he]
  exact totalizationSpectrumComparison_levelwise D hD hΩ n

/-- 通常 Tot の BF 比較射は全整数次数のホモトピー群で同型。 -/
lemma totalizationSpectrumMap_piIsomorphism :
    OmegaSpectrum.PiIsomorphism (totalizationSpectrumMap D hD hΩ) :=
  OmegaSpectrum.piIsomorphism_of_levelwise _ (totalizationSpectrumMap_levelwise D hD hΩ)

end
end SerrePositivity.KST.Spectra.KanSequence
