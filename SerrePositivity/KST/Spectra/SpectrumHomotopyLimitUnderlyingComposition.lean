module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitComposition
public import SerrePositivity.KST.Spectra.RawSpectrumWeightedCompositionUnderlying

/-!
概要：BF Hom の元の比較の源自然性を、共有の通常の weighted end の作用へ移す。
方針：全 Hom パラメータの点つき自然性を忘れ、smash 商と end の作用の照合を適用する。
規約：基点を忘れた元の係数図式を使う。使われ方：coherent 錐の普遍切断の前合成公式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum
variable {I : Type u} [SmallCategory I]

/-- 元の BF Hom 比較を、基点を忘れた元の Hom 係数の weighted end に送る。 -/
def homotopyLimitUnderlyingMappingComparison (X : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) :
    mappingSpace X (homotopyLimit D) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
        (((D ⋙ forgetToKan) ⋙ RawSpectrumMapping.pointedFunctor X) ⋙
          PointedSimplicialSet.forget) :=
  (homotopyLimitPointedMappingComparison X D).right ≫
    (PointedWeightedEnd.underlyingIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
      ((D ⋙ forgetToKan) ⋙ RawSpectrumMapping.pointedFunctor X)).hom

/-- 元の BF Hom 比較は、共有の weighted end の全 Hom パラメータの作用に自然。 -/
lemma homotopyLimitUnderlyingMappingComparison_composition (X Y : OmegaSpectrum.{u})
    (D : I ⥤ OmegaSpectrum.{u}) :
    mappingComposition X Y (homotopyLimit D) ≫ homotopyLimitUnderlyingMappingComparison X D =
      (𝟙 (mappingSpace X Y) ⊗ₘ homotopyLimitUnderlyingMappingComparison Y D) ≫
        RawSpectrumMapping.unpointedWeightedComposition X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
          (D ⋙ forgetToKan) := by
  have h := congrArg Under.Hom.right
    (homotopyLimitPointedMappingComparison_composition X Y D)
  have hp := congrArg (fun f ↦
    PointedSimplicialSet.productToSmash
      (RawSpectrumMapping.pointedSpace X Y.toKanSequence)
      (RawSpectrumMapping.pointedSpace Y (homotopyLimit D).toKanSequence) ≫ f) h
  simp only [Under.comp_right] at hp
  rw [← Category.assoc, RawSpectrumMapping.productToSmash_pointedComposition] at hp
  erw [← reassoc_of% PointedSimplicialSet.productToSmash_naturality
    (𝟙 (RawSpectrumMapping.pointedSpace X Y.toKanSequence))
    (homotopyLimitPointedMappingComparison Y D)] at hp
  rw [RawSpectrumMapping.composition_spectrum, Under.id_right] at hp
  dsimp only [homotopyLimitUnderlyingMappingComparison]
  rw [← Category.assoc]
  erw [hp]
  simp only [Category.assoc]
  erw [RawSpectrumMapping.weightedComposition_underlyingIso]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
