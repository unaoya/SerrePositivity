module

public import SerrePositivity.KST.Spectra.RawSpectrumHomotopyLimitComposition
public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitMappingEquivalence

/-!
概要：元の BF Hom–end 比較は、源の全 Hom パラメータによる合成と可換。
方針：BF 射影の後合成と raw Hom–end 交換の二つの豊穣自然性を合成する。
規約：元の同値の順射を変更しない。使われ方：γ3 の coherent 錐の構成への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum
variable {I : Type u} [SmallCategory I]
local instance homotopyCompositionCoefficientKan (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) (i : I) :
    KanComplex ((((D ⋙ forgetToKan) ⋙ RawSpectrumMapping.pointedFunctor X).obj i).right) :=
  RawSpectrumMapping.pointedSpace_kanComplex X (D.obj i).toKanSequence

/-- 元の BF Hom–end 比較を、零写像を基点とする実際の点つき射として取る。 -/
def homotopyLimitPointedMappingComparison (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) :
    RawSpectrumMapping.pointedSpace X (homotopyLimit D).toKanSequence ⟶
      PointedWeightedEnd.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
        ((D ⋙ forgetToKan) ⋙ RawSpectrumMapping.pointedFunctor X) :=
  RawSpectrumMapping.pointedPost X (homotopyLimitProjection D) ≫
    (RawSpectrumMapping.homotopyLimitIso X (D ⋙ forgetToKan)).hom

/-- 点つき比較を忘れた順射は、既存の実際の同値の順射そのもの。 -/
lemma homotopyLimitPointedMappingComparison_right (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) :
    (homotopyLimitPointedMappingComparison X D).right =
      (homotopyLimitMappingEquivalence X D).hom := rfl

/-- 元の BF Hom–end 比較の、全 Hom パラメータの合成に関する厳密な自然性。 -/
lemma homotopyLimitPointedMappingComparison_composition (X Y : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) :
    RawSpectrumMapping.pointedComposition X Y (homotopyLimit D).toKanSequence ≫
        homotopyLimitPointedMappingComparison X D =
      (𝟙 (RawSpectrumMapping.pointedSpace X Y.toKanSequence) ⊗ₘ
        homotopyLimitPointedMappingComparison Y D) ≫
          RawSpectrumMapping.weightedComposition X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (D ⋙ forgetToKan) := by
  dsimp only [homotopyLimitPointedMappingComparison]
  rw [← Category.assoc, RawSpectrumMapping.pointedComposition_post,
    Category.assoc, RawSpectrumMapping.homotopyLimitIso_composition,
    ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]

end SerrePositivity.KST.Spectra.OmegaSpectrum
