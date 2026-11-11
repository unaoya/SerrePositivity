module
public import SerrePositivity.KST.SConstruction.SuspensionLoopEnrichedComposition
public import SerrePositivity.KST.SConstruction.PointedLoopEnrichment

/-! # Suspension–loop 随伴と全写像パラメータの後合成
概要：標的の射自体も単体パラメータで動かしたときの、逆随伴と後合成の整合性。
方針：逆随伴を suspension と余単位に分解し、豊穣合成の中間射を移動する。
規約：元の点つき模型と全単体次数の合成を保ち、Kan 性を仮定しない。
使われ方：元の全入力変換を suspension 側へ移すための両変数の豊穣自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open Spectra

/-- 逆随伴の写像空間の作用は、suspension と元の余単位への後合成に分解する。 -/
lemma suspensionLoopPointedMappingIso_inv_factor (X Y : PointedSimplicialSet.{u}) :
    (suspensionLoopPointedMappingIso X Y).inv =
      suspensionHom X (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) ≫
        (ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X)).map ((ihom.ev PointedSimplicialSet.circle.{u}).app Y) := by
  change ihomUncurry PointedSimplicialSet.circle.{u} X Y =
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map PointedSimplicialSet.circle.{u} X
        ((ihom PointedSimplicialSet.circle.{u}).obj Y) ≫
      (ihom (PointedSimplicialSet.circle.{u} ⊗ X)).map
        ((ihom.ev PointedSimplicialSet.circle.{u}).app Y)
  apply uncurry_injective
  rw [uncurry_ihomUncurry, uncurry_natural_right, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map, uncurry_curry]
  exact (Category.assoc _ _ _).symm

/-- Loop の写像空間の作用を逆随伴で戻すと、元の余単位による前合成になる。 -/
lemma pointedLoopHom_uncurry (Y Z : PointedSimplicialSet.{u}) :
    pointedLoopHom Y Z ≫ (suspensionLoopPointedMappingIso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) Z).inv =
      (MonoidalClosed.pre ((ihom.ev PointedSimplicialSet.circle.{u}).app Y)).app Z := by
  change curry (MonoidalClosed.comp PointedSimplicialSet.circle.{u} Y Z) ≫
      ihomUncurry PointedSimplicialSet.circle.{u}
        ((ihom PointedSimplicialSet.circle.{u}).obj Y) Z =
    (MonoidalClosed.pre ((ihom.ev PointedSimplicialSet.circle.{u}).app Y)).app Z
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_ihomUncurry, uncurry_pre]
  rw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc,
    whiskerLeft_curry_ihom_ev_app]
  have hev : PointedSimplicialSet.circle.{u} ◁
      MonoidalClosed.comp PointedSimplicialSet.circle.{u} Y Z ≫
        (ihom.ev PointedSimplicialSet.circle.{u}).app Z =
    (α_ PointedSimplicialSet.circle.{u}
      ((ihom PointedSimplicialSet.circle.{u}).obj Y) ((ihom Y).obj Z)).inv ≫
        (ihom.ev PointedSimplicialSet.circle.{u}).app Y ▷ ((ihom Y).obj Z) ≫
          (ihom.ev Y).app Z :=
    uncurry_curry (MonoidalClosed.compTranspose PointedSimplicialSet.circle.{u} Y Z)
  rw [hev, Iso.hom_inv_id_assoc]
  rfl

/-- 逆随伴は、標的の射を写像空間全体で動かす後合成と厳密に整合する。 -/
lemma suspensionLoopPointedMappingIso_inv_enriched_post
    (X Y Z : PointedSimplicialSet.{u}) :
    (𝟙 (PointedObject.basedHom X (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)) ⊗ₘ pointedLoopHom Y Z) ≫
        MonoidalClosed.comp X (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z) ≫
          (suspensionLoopPointedMappingIso X Z).inv =
      ((suspensionLoopPointedMappingIso X Y).inv ⊗ₘ
        𝟙 (PointedObject.basedHom Y Z)) ≫ MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) Y Z := by
  let : EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
    enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}
  have hm := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_comp_middle PointedSimplicialSet.{u} (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X)
    ((ihom.ev PointedSimplicialSet.circle.{u}).app Y) Z
  simp only [enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    enrichedOrdinaryCategorySelf_eHomWhiskerRight, enrichedCategorySelf_comp] at hm
  change ((ihom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X)).map ((ihom.ev PointedSimplicialSet.circle.{u}).app Y) ▷
      PointedObject.basedHom Y Z) ≫ MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) Y Z =
    PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)) ◁
        (MonoidalClosed.pre ((ihom.ev PointedSimplicialSet.circle.{u}).app Y)).app Z ≫
      MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)) Z at hm
  rw [suspensionLoopPointedMappingIso_inv_enriched_pre,
    ← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Category.id_comp]
  rw [pointedLoopHom_uncurry, tensorHom_def, Category.assoc, ← hm,
    ← Category.assoc, ← comp_whiskerRight]
  rw [← suspensionLoopPointedMappingIso_inv_factor]
  simp only [tensorHom_id]

/-- 順随伴も標的射の豊穣後合成を保つ。 -/
lemma suspensionLoopPointedMappingIso_enriched_post
    (X Y Z : PointedSimplicialSet.{u}) :
    MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) Y Z ≫ (suspensionLoopPointedMappingIso X Z).hom =
      ((suspensionLoopPointedMappingIso X Y).hom ⊗ₘ pointedLoopHom Y Z) ≫
        MonoidalClosed.comp X (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z) := by
  apply (cancel_epi ((suspensionLoopPointedMappingIso X Y).inv ⊗ₘ
    𝟙 (PointedObject.basedHom Y Z))).mp
  rw [← Category.assoc, ← suspensionLoopPointedMappingIso_inv_enriched_post]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Iso.inv_hom_id, Category.id_comp]

private lemma pointedSmashForget_composite {A A' B B' C : PointedSimplicialSet.{u}}
    (f : A ⟶ A') (g : B ⟶ B') (h : A' ⊗ B' ⟶ C) :
    (f.right ⊗ₘ g.right) ≫ PointedSimplicialSet.productToSmash A' B' ≫ h.right =
      PointedSimplicialSet.productToSmash A B ≫ ((f ⊗ₘ g) ≫ h).right := by
  rw [Under.comp_right, ← Category.assoc, PointedSimplicialSet.productToSmash_naturality,
    Category.assoc]

/-- 基点固定写像空間の全単体の後合成は、逆随伴による移送と厳密に可換。 -/
lemma suspensionLoopMappingIso_inv_enriched_post
    (X Y Z : PointedSimplicialSet.{u}) :
    (𝟙 (PointedObject.basedHom X (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right ⊗ₘ (pointedLoopHom Y Z).right) ≫
        pointedMappingComposition X (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z) ≫
          (suspensionLoopMappingIso X Z).inv =
      ((suspensionLoopMappingIso X Y).inv ⊗ₘ
        𝟙 (PointedObject.basedHom Y Z).right) ≫
          pointedMappingComposition (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) Y Z := by
  change ((show PointedObject.basedHom X (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) ⟶
      PointedObject.basedHom X (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) from 𝟙 _).right ⊗ₘ
      (pointedLoopHom Y Z).right) ≫ PointedSimplicialSet.productToSmash _ _ ≫
        (MonoidalClosed.comp X (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z)).right ≫
          (suspensionLoopPointedMappingIso X Z).inv.right =
    ((suspensionLoopPointedMappingIso X Y).inv.right ⊗ₘ
      (show PointedObject.basedHom Y Z ⟶ PointedObject.basedHom Y Z from 𝟙 _).right) ≫
        PointedSimplicialSet.productToSmash _ _ ≫
          (MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) Y Z).right
  rw [← Under.comp_right, pointedSmashForget_composite, pointedSmashForget_composite,
    suspensionLoopPointedMappingIso_inv_enriched_post]

/-- 独立な二つの単体パラメータを持つ後合成の族を、同時に suspension 側へ移す。 -/
lemma suspensionLoopMappingFamilies_inv_post {P Q : SSet.{u}}
    {X Y Z : PointedSimplicialSet.{u}}
    (a : P ⟶ (PointedObject.basedHom X (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right)
    (b : Q ⟶ (PointedObject.basedHom Y Z).right) :
    (a ⊗ₘ (b ≫ (pointedLoopHom Y Z).right)) ≫
        pointedMappingComposition X (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z) ≫
          (suspensionLoopMappingIso X Z).inv =
      ((a ≫ (suspensionLoopMappingIso X Y).inv) ⊗ₘ b) ≫
        pointedMappingComposition (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) Y Z := by
  have h := congrArg (fun k => (a ⊗ₘ b) ≫ k)
    (suspensionLoopMappingIso_inv_enriched_post X Y Z)
  simpa only [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id] using h

end SerrePositivity.KST.SConstruction
