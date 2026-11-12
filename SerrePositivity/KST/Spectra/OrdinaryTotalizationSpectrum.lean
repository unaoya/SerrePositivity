module

public import SerrePositivity.KST.Spectra.OrdinaryTotalizationSequence

/-!
概要：通常 Tot の Kan Ω 列の BF 模型と、BK end を介する BF homotopy Tot 比較。
方針：通常 Tot の構造を単射置換し、二つの BF 模型から共通の BK end の列へ送る。
規約：全て実際の構造可換射であり、各段の全基点 π 同型を証明する。
使われ方：BF 1978 §2、Goerss–Jardine VIII §1。Sp-4 の通常 Tot の BF 比較。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.KanSequence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 通常 Tot を各段に持つ Ω 列の BF 単射置換。 -/
def totalizationSpectrum (D : CosimplicialObject KanSequence.{u})
    (hD : TotalizationReedy D) (hΩ : ∀ j, (D.obj j).OmegaCondition) : OmegaSpectrum.{u} :=
  (totalizationKan D hD).cofibrantOmegaSpectrum (totalizationKan_omegaCondition D hD hΩ)

/-- 通常 Tot の BF 模型から共通の BK end の列への実際の比較。 -/
def totalizationSpectrumComparison (D : CosimplicialObject KanSequence.{u})
    (hD : TotalizationReedy D) (hΩ : ∀ j, (D.obj j).OmegaCondition) :
    Hom (totalizationSpectrum D hD hΩ).toKanSequence (homotopyLimit (AsSmall.down ⋙ D)) :=
  (replacementProjection (totalizationKan D hD)).comp (totalizationKanComparison D hD)

/-- 通常 Tot の BF 比較は各段で全基点 π 同型。 -/
lemma totalizationSpectrumComparison_levelwise (D : CosimplicialObject KanSequence.{u})
    (hD : TotalizationReedy D) (hΩ : ∀ j, (D.obj j).OmegaCondition) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((totalizationSpectrumComparison D hD hΩ).app n).right :=
  (replacementProjection_piIsomorphism (totalizationKan D hD) n).comp
    (totalizationKanComparison_levelwise D hD n)

/-- BF homotopy Tot から同じ BK end の列への比較。 -/
def homotopyTotalizationComparison (D : CosimplicialObject KanSequence.{u})
    (hΩ : ∀ j, (D.obj j).OmegaCondition) :
    Hom (homotopyLimitSpectrum (AsSmall.down ⋙ D)
      (fun j ↦ hΩ (AsSmall.down.obj j))).toKanSequence (homotopyLimit (AsSmall.down ⋙ D)) :=
  homotopyLimitProjection (AsSmall.down ⋙ D) (fun j ↦ hΩ (AsSmall.down.obj j))

/-- もう一方の BF 比較も各段で全基点 π 同型。 -/
lemma homotopyTotalizationComparison_levelwise (D : CosimplicialObject KanSequence.{u})
    (hΩ : ∀ j, (D.obj j).OmegaCondition) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((homotopyTotalizationComparison D hΩ).app n).right :=
  homotopyLimitProjection_levelwise (AsSmall.down ⋙ D)
    (fun j ↦ hΩ (AsSmall.down.obj j)) n

end
end SerrePositivity.KST.Spectra.KanSequence
