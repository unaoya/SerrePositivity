module
public import SerrePositivity.KST.SConstruction.EnrichedFixedCompositionMaps
public import SerrePositivity.KST.Spectra.SpectrumSimplicialCategory

/-! # 固定因子との全 BF 合成の各段評価
概要：固定した BF 射との全豊穣合成を評価すると、同じ段の固定頂点との全合成になる。
方針：BF 合成の各段評価式を、固定頂点と元の全 Hom の射対に制限する。
規約：成分の計算ではなく全単体集合の実射の等号を与える。
使われ方：元の BF 比較辺の定数な零段を、両 whisker の定数な零段へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
local instance fixedFactorEvaluationPointedSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
local instance fixedFactorEvaluationSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 固定第一射との全合成は、各段で同じ評価頂点との合成を厳密に回収する。 -/
lemma spectrumFixedLeftComposition_evaluation {W X Z : OmegaSpectrum.{u}} (f : W ⟶ X) (n : ℕ) :
    enrichedFixedLeftComposition (Z := Z) f ≫ OmegaSpectrum.evaluation W Z n =
      OmegaSpectrum.evaluation X Z n ≫
        lift (SSet.const ((OmegaSpectrum.evaluation W X n).app (Opposite.op ⦋0⦌)
          (SimplicialCategory.homEquiv' _ _ f))) (𝟙 _) ≫
            eComp SSet (W.level n).space (X.level n).space (Z.level n).space := by
  change (lift (SSet.const (SimplicialCategory.homEquiv' _ _ f)) (𝟙 _) ≫
    OmegaSpectrum.mappingComposition W X Z) ≫ _ = _
  rw [Category.assoc, OmegaSpectrum.mappingComposition_evaluation]
  simp only [OmegaSpectrum.compositionFamily, ← Category.assoc]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, lift_fst, SSet.comp_const]
    rw [← Category.assoc, lift_fst, SSet.const_comp]
  · simp only [Category.assoc, tensorHom_snd, lift_snd, Category.comp_id]
    rw [← Category.assoc, lift_snd (X := OmegaSpectrum.mappingSpace W X)
      (SSet.const (SimplicialCategory.homEquiv' W X f))
      (𝟙 (OmegaSpectrum.mappingSpace X Z)), Category.id_comp]

/-- 固定最終射との全合成も、各段で同じ評価頂点との合成を厳密に回収する。 -/
lemma spectrumFixedRightComposition_evaluation {W Y Z : OmegaSpectrum.{u}} (h : Y ⟶ Z) (n : ℕ) :
    enrichedFixedRightComposition (W := W) h ≫ OmegaSpectrum.evaluation W Z n =
      OmegaSpectrum.evaluation W Y n ≫
        lift (𝟙 _) (SSet.const ((OmegaSpectrum.evaluation Y Z n).app (Opposite.op ⦋0⦌)
          (SimplicialCategory.homEquiv' _ _ h))) ≫
            eComp SSet (W.level n).space (Y.level n).space (Z.level n).space := by
  change (lift (𝟙 _) (SSet.const (SimplicialCategory.homEquiv' _ _ h)) ≫
    OmegaSpectrum.mappingComposition W Y Z) ≫ _ = _
  rw [Category.assoc, OmegaSpectrum.mappingComposition_evaluation]
  simp only [OmegaSpectrum.compositionFamily, ← Category.assoc]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, lift_fst, Category.comp_id]
    rw [← Category.assoc, lift_fst (Y := OmegaSpectrum.mappingSpace Y Z)
      (𝟙 (OmegaSpectrum.mappingSpace W Y))
      (SSet.const (SimplicialCategory.homEquiv' Y Z h)), Category.id_comp]
  · simp only [Category.assoc, tensorHom_snd, lift_snd, SSet.comp_const]
    rw [← Category.assoc, lift_snd, SSet.const_comp]

end SerrePositivity.KST.SConstruction
