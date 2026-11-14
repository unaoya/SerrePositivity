module

public import SerrePositivity.KST.Spectra.SpectrumCotensorCompatibleComposition
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedParameterUnits

/-!
概要：cotensor の整合写像空間の恒等射と、合成の圏の法則。
方針：恒等射の可換性を単位律から得て、全ての法則を二つの射影で検査する。
規約：点つき豊穣圏の厳密な単位・結合律。
使われ方：coherent な cotensor 関手の供給。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
local instance compatibleLawsPointedEnrichment :
    EnrichedCategory PointedSimplicialSet.{u} OmegaSpectrum.{u} := pointedEnrichment

/-- 整合写像空間への射は、二つの射影で決まる。 -/
lemma hom_ext (A : PointedSimplicialSet.{u}) (X Y : OmegaSpectrum.{u})
    {T : PointedSimplicialSet.{u}} {f g : T ⟶ pointedSpace A X Y}
    (hc : f ≫ cotensorMap A X Y = g ≫ cotensorMap A X Y)
    (hs : f ≫ sourceMap A X Y = g ≫ sourceMap A X Y) : f = g :=
  pullback.hom_ext hc hs

/-- 元の恒等射と cotensor の恒等射は普遍評価と可換。 -/
lemma identity_condition (A : PointedSimplicialSet.{u}) (X : OmegaSpectrum.{u}) :
    RawSpectrumMapping.pointedIdentity (cotensor A X) ≫
        cotensorEvaluationPrecomposition (cotensor A X) X A =
      RawSpectrumMapping.pointedIdentity X ≫ evaluationPost A X X := by
  apply (condition_iff A X X _ _).mpr
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_parameter_square_id PointedSimplicialSet.{u}
    (C := OmegaSpectrum.{u}) (X := cotensor A X) (Y := X) (cotensorEvaluation A X)

/-- 二つの元の恒等射の組。 -/
def identity (A : PointedSimplicialSet.{u}) (X : OmegaSpectrum.{u}) :
    𝟙_ PointedSimplicialSet.{u} ⟶ pointedSpace A X X :=
  pullback.lift (RawSpectrumMapping.pointedIdentity (cotensor A X))
    (RawSpectrumMapping.pointedIdentity X) (identity_condition A X)

@[reassoc (attr := simp)]
lemma identity_cotensorMap (A : PointedSimplicialSet.{u}) (X : OmegaSpectrum.{u}) :
    identity A X ≫ cotensorMap A X X = RawSpectrumMapping.pointedIdentity (cotensor A X) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma identity_sourceMap (A : PointedSimplicialSet.{u}) (X : OmegaSpectrum.{u}) :
    identity A X ≫ sourceMap A X X = RawSpectrumMapping.pointedIdentity X :=
  pullback.lift_snd _ _ _

/-- 整合写像空間の合成の左単位律。 -/
lemma identity_composition (A : PointedSimplicialSet.{u}) (X Y : OmegaSpectrum.{u}) :
    (λ_ (pointedSpace A X Y)).inv ≫ identity A X ▷ pointedSpace A X Y ≫
      composition A X X Y = 𝟙 _ := by
  apply hom_ext A X Y
  · simp only [Category.assoc, composition_cotensorMap, Category.id_comp]
    rw [whiskerRight_comp_tensorHom_assoc, identity_cotensorMap,
      leftUnitor_inv_comp_tensorHom_assoc]
    exact (congrArg (fun k ↦ cotensorMap A X Y ≫ k)
      (RawSpectrumMapping.pointedIdentity_composition (cotensor A X)
        (cotensor A Y).toKanSequence)).trans (Category.comp_id _)
  · simp only [Category.assoc, composition_sourceMap, Category.id_comp]
    rw [whiskerRight_comp_tensorHom_assoc, identity_sourceMap,
      leftUnitor_inv_comp_tensorHom_assoc]
    exact (congrArg (fun k ↦ sourceMap A X Y ≫ k)
      (RawSpectrumMapping.pointedIdentity_composition X Y.toKanSequence)).trans (Category.comp_id _)

/-- 整合写像空間の合成の右単位律。 -/
lemma composition_identity (A : PointedSimplicialSet.{u}) (X Y : OmegaSpectrum.{u}) :
    (ρ_ (pointedSpace A X Y)).inv ≫ pointedSpace A X Y ◁ identity A Y ≫
      composition A X Y Y = 𝟙 _ := by
  apply hom_ext A X Y
  · simp only [Category.assoc, composition_cotensorMap, Category.id_comp]
    rw [whiskerLeft_comp_tensorHom_assoc, identity_cotensorMap,
      rightUnitor_inv_comp_tensorHom_assoc]
    exact (congrArg (fun k ↦ cotensorMap A X Y ≫ k)
      (RawSpectrumMapping.pointedComposition_identity (cotensor A X) (cotensor A Y))).trans
        (Category.comp_id _)
  · simp only [Category.assoc, composition_sourceMap, Category.id_comp]
    rw [whiskerLeft_comp_tensorHom_assoc, identity_sourceMap,
      rightUnitor_inv_comp_tensorHom_assoc]
    exact (congrArg (fun k ↦ sourceMap A X Y ≫ k)
      (RawSpectrumMapping.pointedComposition_identity X Y)).trans (Category.comp_id _)

/-- 整合写像空間の合成の結合律。 -/
lemma composition_assoc (A : PointedSimplicialSet.{u}) (W X Y Z : OmegaSpectrum.{u}) :
    (α_ (pointedSpace A W X) (pointedSpace A X Y) (pointedSpace A Y Z)).inv ≫
      composition A W X Y ▷ pointedSpace A Y Z ≫ composition A W Y Z =
      pointedSpace A W X ◁ composition A X Y Z ≫ composition A W X Z := by
  apply hom_ext A W Z
  · simp only [Category.assoc, composition_cotensorMap]
    rw [whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
      composition_cotensorMap, composition_cotensorMap]
    rw [← tensorHom_comp_whiskerRight, ← tensorHom_comp_whiskerLeft,
      Category.assoc, ← associator_inv_naturality_assoc]
    simp only [Category.assoc]
    exact congrArg (fun k ↦
      (cotensorMap A W X ⊗ₘ (cotensorMap A X Y ⊗ₘ cotensorMap A Y Z)) ≫ k)
      (RawSpectrumMapping.pointedComposition_assoc (cotensor A W) (cotensor A X)
        (cotensor A Y) (cotensor A Z).toKanSequence)
  · simp only [Category.assoc, composition_sourceMap]
    rw [whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
      composition_sourceMap, composition_sourceMap]
    rw [← tensorHom_comp_whiskerRight, ← tensorHom_comp_whiskerLeft,
      Category.assoc, ← associator_inv_naturality_assoc]
    simp only [Category.assoc]
    exact congrArg (fun k ↦
      (sourceMap A W X ⊗ₘ (sourceMap A X Y ⊗ₘ sourceMap A Y Z)) ≫ k)
      (RawSpectrumMapping.pointedComposition_assoc W X Y Z.toKanSequence)

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
