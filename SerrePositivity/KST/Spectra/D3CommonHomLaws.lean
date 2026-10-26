module

public import SerrePositivity.KST.Spectra.D3CommonHomComposition

/-!
概要：比較射を保つ共通 Hom の厳密な単位・結合律。
方針：共通 BF Hom と元の FullCompatible Hom への同じ二射影で法則を検査する。
規約：元の包含・比較・右射影を保つ実合成を使用する。
使われ方：d3b② の比較を含む共通解像の局所 Kan な豊穣構造。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 比較 Hom の実合成は厳密な左単位律を満たす。 -/
lemma commonIdentity_composition (X Y : OmegaSpectrum.{u}) :
    (λ_ (commonHom X Y)).inv ≫ commonIdentity X ▷ commonHom X Y ≫
      commonComposition X X Y = 𝟙 _ := by
  apply commonHom_ext X Y
  · simp only [Category.assoc, commonComposition_refined, Category.id_comp]
    rw [whiskerRight_comp_tensorHom_assoc, commonIdentity_refined,
      leftUnitor_inv_comp_tensorHom_assoc]
    exact (congrArg (fun k ↦ commonRefinedMap X Y ≫ k)
      (mappingIdentity_comp (commonRefinement X)
        (commonRefinement Y))).trans (Category.comp_id _)
  · simp only [Category.assoc, commonComposition_base, Category.id_comp]
    rw [whiskerRight_comp_tensorHom_assoc, commonIdentity_base,
      leftUnitor_inv_comp_tensorHom_assoc]
    exact (congrArg (fun k ↦ commonBaseMap X Y ≫ k)
      (fullCompatibleIdentity_composition X Y)).trans (Category.comp_id _)

/-- 概要：整合写像空間の合成の右単位律。
方針：実引き戻しの二つの射影で元の豊穣法則を検査する。
規約：指定左因子と全 Hom パラメータを保持する。
使われ方：相対 BF 比較の豊穣構造。 -/
lemma commonComposition_identity (X Y : OmegaSpectrum.{u}) :
    (ρ_ (commonHom X Y)).inv ≫ commonHom X Y ◁ commonIdentity Y ≫
      commonComposition X Y Y = 𝟙 _ := by
  apply commonHom_ext X Y
  · simp only [Category.assoc, commonComposition_refined, Category.id_comp]
    rw [whiskerLeft_comp_tensorHom_assoc, commonIdentity_refined,
      rightUnitor_inv_comp_tensorHom_assoc]
    exact (congrArg (fun k ↦ commonRefinedMap X Y ≫ k)
      (mappingComposition_identity (commonRefinement X) (commonRefinement Y))).trans
        (Category.comp_id _)
  · simp only [Category.assoc, commonComposition_base, Category.id_comp]
    rw [whiskerLeft_comp_tensorHom_assoc, commonIdentity_base,
      rightUnitor_inv_comp_tensorHom_assoc]
    exact (congrArg (fun k ↦ commonBaseMap X Y ≫ k)
      (fullCompatibleComposition_identity X Y)).trans (Category.comp_id _)

/-- 概要：整合写像空間の合成の結合律。
方針：実引き戻しの二つの射影で元の豊穣法則を検査する。
規約：指定左因子と全 Hom パラメータを保持する。
使われ方：相対 BF 比較の豊穣構造。 -/
lemma commonComposition_assoc (W X Y Z : OmegaSpectrum.{u}) :
    (α_ (commonHom W X) (commonHom X Y)
      (commonHom Y Z)).inv ≫
      commonComposition W X Y ▷ commonHom Y Z ≫ commonComposition W Y Z =
      commonHom W X ◁ commonComposition X Y Z ≫
      commonComposition W X Z := by
  apply commonHom_ext W Z
  · simp only [Category.assoc, commonComposition_refined]
    rw [whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
      commonComposition_refined, commonComposition_refined]
    rw [← tensorHom_comp_whiskerRight, ← tensorHom_comp_whiskerLeft,
      Category.assoc, ← associator_inv_naturality_assoc]
    simp only [Category.assoc]
    exact congrArg (fun k ↦
      (commonRefinedMap W X ⊗ₘ (commonRefinedMap X Y ⊗ₘ commonRefinedMap Y Z)) ≫ k)
      (mappingComposition_assoc (commonRefinement W) (commonRefinement X)
        (commonRefinement Y) (commonRefinement Z))
  · simp only [Category.assoc, commonComposition_base]
    rw [whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
      commonComposition_base, commonComposition_base]
    rw [← tensorHom_comp_whiskerRight, ← tensorHom_comp_whiskerLeft,
      Category.assoc, ← associator_inv_naturality_assoc]
    simp only [Category.assoc]
    exact congrArg (fun k ↦
      (commonBaseMap W X ⊗ₘ (commonBaseMap X Y ⊗ₘ commonBaseMap Y Z)) ≫ k)
      (fullCompatibleComposition_assoc W X Y Z)

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
