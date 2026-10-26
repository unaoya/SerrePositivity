module

public import SerrePositivity.KST.Spectra.AdjointLoopRelativeFullCompatibleUnits

/-!
概要：左右因子を同時に保つ全 Hom の組の厳密な単位・結合律。
方針：二つの実射影で元の BF 豊穣単位・結合律を検査する。
規約：右射影の可換条件を削除して法則を得ることはしない。
使われ方：元の指定単位と右射影を保持する局所 Kan な豊穣圏。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 概要：左右境界を保つ組への全パラメータ族は二つの元の射影で決まる。
方針：実引き戻しの外延性を使う。
規約：全単体上の厳密等式。
使われ方：豊穣単位・結合律の検査。 -/
lemma fullCompatible_hom_ext (X Y : OmegaSpectrum.{u}) {T : SSet.{u}}
    {f g : T ⟶ fullCompatibleSpace X Y}
    (hg : f ≫ fullReplacedMap X Y = g ≫ fullReplacedMap X Y)
    (hf : f ≫ fullOriginalMap X Y = g ≫ fullOriginalMap X Y) : f = g :=
  pullback.hom_ext hg hf

/-- 概要：整合写像空間の合成の左単位律。
方針：実引き戻しの二つの射影で元の豊穣法則を検査する。
規約：指定左因子と全 Hom パラメータを保持する。
使われ方：相対 BF 比較の豊穣構造。 -/
lemma fullCompatibleIdentity_composition (X Y : OmegaSpectrum.{u}) :
    (λ_ (fullCompatibleSpace X Y)).inv ≫ fullCompatibleIdentity X ▷ fullCompatibleSpace X Y ≫
      fullCompatibleComposition X X Y = 𝟙 _ := by
  apply fullCompatible_hom_ext X Y
  · simp only [Category.assoc, fullCompatibleComposition_replacedMap, Category.id_comp]
    rw [whiskerRight_comp_tensorHom_assoc, fullCompatibleIdentity_replacedMap,
      leftUnitor_inv_comp_tensorHom_assoc]
    exact (congrArg (fun k ↦ fullReplacedMap X Y ≫ k)
      (mappingIdentity_comp (middle X)
        (middle Y))).trans (Category.comp_id _)
  · simp only [Category.assoc, fullCompatibleComposition_originalMap, Category.id_comp]
    rw [whiskerRight_comp_tensorHom_assoc, fullCompatibleIdentity_originalMap,
      leftUnitor_inv_comp_tensorHom_assoc]
    exact (congrArg (fun k ↦ fullOriginalMap X Y ≫ k)
      (mappingIdentity_comp X Y)).trans (Category.comp_id _)

/-- 概要：整合写像空間の合成の右単位律。
方針：実引き戻しの二つの射影で元の豊穣法則を検査する。
規約：指定左因子と全 Hom パラメータを保持する。
使われ方：相対 BF 比較の豊穣構造。 -/
lemma fullCompatibleComposition_identity (X Y : OmegaSpectrum.{u}) :
    (ρ_ (fullCompatibleSpace X Y)).inv ≫ fullCompatibleSpace X Y ◁ fullCompatibleIdentity Y ≫
      fullCompatibleComposition X Y Y = 𝟙 _ := by
  apply fullCompatible_hom_ext X Y
  · simp only [Category.assoc, fullCompatibleComposition_replacedMap, Category.id_comp]
    rw [whiskerLeft_comp_tensorHom_assoc, fullCompatibleIdentity_replacedMap,
      rightUnitor_inv_comp_tensorHom_assoc]
    exact (congrArg (fun k ↦ fullReplacedMap X Y ≫ k)
      (mappingComposition_identity (middle X) (middle Y))).trans
        (Category.comp_id _)
  · simp only [Category.assoc, fullCompatibleComposition_originalMap, Category.id_comp]
    rw [whiskerLeft_comp_tensorHom_assoc, fullCompatibleIdentity_originalMap,
      rightUnitor_inv_comp_tensorHom_assoc]
    exact (congrArg (fun k ↦ fullOriginalMap X Y ≫ k)
      (mappingComposition_identity X Y)).trans (Category.comp_id _)

/-- 概要：整合写像空間の合成の結合律。
方針：実引き戻しの二つの射影で元の豊穣法則を検査する。
規約：指定左因子と全 Hom パラメータを保持する。
使われ方：相対 BF 比較の豊穣構造。 -/
lemma fullCompatibleComposition_assoc (W X Y Z : OmegaSpectrum.{u}) :
    (α_ (fullCompatibleSpace W X) (fullCompatibleSpace X Y)
      (fullCompatibleSpace Y Z)).inv ≫
      fullCompatibleComposition W X Y ▷ fullCompatibleSpace Y Z ≫ fullCompatibleComposition W Y Z =
      fullCompatibleSpace W X ◁ fullCompatibleComposition X Y Z ≫
      fullCompatibleComposition W X Z := by
  apply fullCompatible_hom_ext W Z
  · simp only [Category.assoc, fullCompatibleComposition_replacedMap]
    rw [whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
      fullCompatibleComposition_replacedMap, fullCompatibleComposition_replacedMap]
    rw [← tensorHom_comp_whiskerRight, ← tensorHom_comp_whiskerLeft,
      Category.assoc, ← associator_inv_naturality_assoc]
    simp only [Category.assoc]
    exact congrArg (fun k ↦
      (fullReplacedMap W X ⊗ₘ (fullReplacedMap X Y ⊗ₘ fullReplacedMap Y Z)) ≫ k)
      (mappingComposition_assoc (middle W) (middle X)
        (middle Y) (middle Z))
  · simp only [Category.assoc, fullCompatibleComposition_originalMap]
    rw [whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
      fullCompatibleComposition_originalMap, fullCompatibleComposition_originalMap]
    rw [← tensorHom_comp_whiskerRight, ← tensorHom_comp_whiskerLeft,
      Category.assoc, ← associator_inv_naturality_assoc]
    simp only [Category.assoc]
    exact congrArg (fun k ↦
      (fullOriginalMap W X ⊗ₘ (fullOriginalMap X Y ⊗ₘ fullOriginalMap Y Z)) ≫ k)
      (mappingComposition_assoc W X Y Z)

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
