module

public import SerrePositivity.KST.Spectra.AdjointLoopRelativeCompatibleComposition
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedParameterUnits

/-!
概要：相対 BF 左因子と可換な全 Hom の組の単位と圏の法則。
方針：実引き戻しの二射影で元の BF 豊穣構造の法則を検査する。
規約：置換の選択に通常の関手法則を仮定しない。
使われ方：相対 BF 比較を保持する局所 Kan な豊穣圏。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance relativeCompatibleLawsPointedEnrichment :
    EnrichedCategory PointedSimplicialSet.{u} OmegaSpectrum.{u} := pointedEnrichment

/-- 概要：整合写像空間への射は、二つの射影で決まる。
方針：実引き戻しの二つの射影で元の豊穣法則を検査する。
規約：指定左因子と全 Hom パラメータを保持する。
使われ方：相対 BF 比較の豊穣構造。 -/
lemma compatible_hom_ext (X Y : OmegaSpectrum.{u})
    {T : PointedSimplicialSet.{u}} {f g : T ⟶ compatibleSpace X Y}
    (hc : f ≫ replacedMap X Y = g ≫ replacedMap X Y)
    (hs : f ≫ originalMap X Y = g ≫ originalMap X Y) : f = g :=
  pullback.hom_ext hc hs

/-- 概要：元の恒等射と相対 BF 置換の恒等射は指定左因子と可換。
方針：実引き戻しの二つの射影で元の豊穣法則を検査する。
規約：指定左因子と全 Hom パラメータを保持する。
使われ方：相対 BF 比較の豊穣構造。 -/
lemma compatibleIdentity_condition (X : OmegaSpectrum.{u}) :
    RawSpectrumMapping.pointedIdentity (middle X) ≫
        RawSpectrumMapping.pointedPre (inclusion X) (middle X).toKanSequence =
      RawSpectrumMapping.pointedIdentity X ≫ inclusionPost X X := by
  apply (compatible_condition_iff X X _ _).mpr
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_parameter_square_id PointedSimplicialSet.{u}
    (C := OmegaSpectrum.{u}) (X := X) (Y := middle X) (inclusionPoint X)

/-- 概要：二つの元の恒等射の組。
方針：実引き戻しの二つの射影で元の豊穣法則を検査する。
規約：指定左因子と全 Hom パラメータを保持する。
使われ方：相対 BF 比較の豊穣構造。 -/
def compatibleIdentity (X : OmegaSpectrum.{u}) :
    𝟙_ PointedSimplicialSet.{u} ⟶ compatibleSpace X X :=
  pullback.lift (RawSpectrumMapping.pointedIdentity (middle X))
    (RawSpectrumMapping.pointedIdentity X) (compatibleIdentity_condition X)

/-- 概要：組の恒等射の射影は元の恒等射。
方針：実引き戻しの射影式を使う。
規約：全単体上の等式。
使われ方：相対 BF 比較の単位法則。 -/
@[reassoc (attr := simp)]
lemma compatibleIdentity_replacedMap (X : OmegaSpectrum.{u}) :
    compatibleIdentity X ≫ replacedMap X X = RawSpectrumMapping.pointedIdentity (middle X) :=
  pullback.lift_fst _ _ _

/-- 概要：組の恒等射の射影は元の恒等射。
方針：実引き戻しの射影式を使う。
規約：全単体上の等式。
使われ方：相対 BF 比較の単位法則。 -/
@[reassoc (attr := simp)]
lemma compatibleIdentity_originalMap (X : OmegaSpectrum.{u}) :
    compatibleIdentity X ≫ originalMap X X = RawSpectrumMapping.pointedIdentity X :=
  pullback.lift_snd _ _ _

/-- 概要：整合写像空間の合成の左単位律。
方針：実引き戻しの二つの射影で元の豊穣法則を検査する。
規約：指定左因子と全 Hom パラメータを保持する。
使われ方：相対 BF 比較の豊穣構造。 -/
lemma compatibleIdentity_composition (X Y : OmegaSpectrum.{u}) :
    (λ_ (compatibleSpace X Y)).inv ≫ compatibleIdentity X ▷ compatibleSpace X Y ≫
      compatibleComposition X X Y = 𝟙 _ := by
  apply compatible_hom_ext X Y
  · simp only [Category.assoc, compatibleComposition_replacedMap, Category.id_comp]
    rw [whiskerRight_comp_tensorHom_assoc, compatibleIdentity_replacedMap,
      leftUnitor_inv_comp_tensorHom_assoc]
    exact (congrArg (fun k ↦ replacedMap X Y ≫ k)
      (RawSpectrumMapping.pointedIdentity_composition (middle X)
        (middle Y).toKanSequence)).trans (Category.comp_id _)
  · simp only [Category.assoc, compatibleComposition_originalMap, Category.id_comp]
    rw [whiskerRight_comp_tensorHom_assoc, compatibleIdentity_originalMap,
      leftUnitor_inv_comp_tensorHom_assoc]
    exact (congrArg (fun k ↦ originalMap X Y ≫ k)
      (RawSpectrumMapping.pointedIdentity_composition X Y.toKanSequence)).trans (Category.comp_id _)

/-- 概要：整合写像空間の合成の右単位律。
方針：実引き戻しの二つの射影で元の豊穣法則を検査する。
規約：指定左因子と全 Hom パラメータを保持する。
使われ方：相対 BF 比較の豊穣構造。 -/
lemma compatibleComposition_identity (X Y : OmegaSpectrum.{u}) :
    (ρ_ (compatibleSpace X Y)).inv ≫ compatibleSpace X Y ◁ compatibleIdentity Y ≫
      compatibleComposition X Y Y = 𝟙 _ := by
  apply compatible_hom_ext X Y
  · simp only [Category.assoc, compatibleComposition_replacedMap, Category.id_comp]
    rw [whiskerLeft_comp_tensorHom_assoc, compatibleIdentity_replacedMap,
      rightUnitor_inv_comp_tensorHom_assoc]
    exact (congrArg (fun k ↦ replacedMap X Y ≫ k)
      (RawSpectrumMapping.pointedComposition_identity (middle X) (middle Y))).trans
        (Category.comp_id _)
  · simp only [Category.assoc, compatibleComposition_originalMap, Category.id_comp]
    rw [whiskerLeft_comp_tensorHom_assoc, compatibleIdentity_originalMap,
      rightUnitor_inv_comp_tensorHom_assoc]
    exact (congrArg (fun k ↦ originalMap X Y ≫ k)
      (RawSpectrumMapping.pointedComposition_identity X Y)).trans (Category.comp_id _)

/-- 概要：整合写像空間の合成の結合律。
方針：実引き戻しの二つの射影で元の豊穣法則を検査する。
規約：指定左因子と全 Hom パラメータを保持する。
使われ方：相対 BF 比較の豊穣構造。 -/
lemma compatibleComposition_assoc (W X Y Z : OmegaSpectrum.{u}) :
    (α_ (compatibleSpace W X) (compatibleSpace X Y) (compatibleSpace Y Z)).inv ≫
      compatibleComposition W X Y ▷ compatibleSpace Y Z ≫ compatibleComposition W Y Z =
      compatibleSpace W X ◁ compatibleComposition X Y Z ≫ compatibleComposition W X Z := by
  apply compatible_hom_ext W Z
  · simp only [Category.assoc, compatibleComposition_replacedMap]
    rw [whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
      compatibleComposition_replacedMap, compatibleComposition_replacedMap]
    rw [← tensorHom_comp_whiskerRight, ← tensorHom_comp_whiskerLeft,
      Category.assoc, ← associator_inv_naturality_assoc]
    simp only [Category.assoc]
    exact congrArg (fun k ↦
      (replacedMap W X ⊗ₘ (replacedMap X Y ⊗ₘ replacedMap Y Z)) ≫ k)
      (RawSpectrumMapping.pointedComposition_assoc (middle W) (middle X)
        (middle Y) (middle Z).toKanSequence)
  · simp only [Category.assoc, compatibleComposition_originalMap]
    rw [whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
      compatibleComposition_originalMap, compatibleComposition_originalMap]
    rw [← tensorHom_comp_whiskerRight, ← tensorHom_comp_whiskerLeft,
      Category.assoc, ← associator_inv_naturality_assoc]
    simp only [Category.assoc]
    exact congrArg (fun k ↦
      (originalMap W X ⊗ₘ (originalMap X Y ⊗ₘ originalMap Y Z)) ≫ k)
      (RawSpectrumMapping.pointedComposition_assoc W X Y Z.toKanSequence)

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
