module
public import SerrePositivity.KST.SConstruction.SuspensionLoopMappingIso
public import SerrePositivity.KST.Spectra.SuspensionComposition
public import SerrePositivity.KST.SConstruction.PointedMappingCompositionFamilies

/-! # Suspension–loop 随伴と全写像パラメータの合成
概要：入力射そのものを単体パラメータで動かしたときの、逆随伴と前合成の整合性。
方針：点つき内部 Hom の評価へ戻し、suspension の豊穣作用と結合子を照合する。
規約：零次の射だけでなく写像空間全体の合成を扱い、Kan 性を仮定しない。
使われ方：全入力の coherent 変換を元の suspension 構造射へ移すための合成条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open Spectra

/-- 逆随伴は、入力射を写像空間全体で動かす前合成と厳密に整合する。 -/
lemma suspensionLoopPointedMappingIso_inv_enriched_pre
    (X Y Z : PointedSimplicialSet.{u}) :
    MonoidalClosed.comp X Y (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z) ≫ (suspensionLoopPointedMappingIso X Z).inv =
      (suspensionHom X Y ⊗ₘ (suspensionLoopPointedMappingIso Y Z).inv) ≫
        MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y) Z := by
  change MonoidalClosed.comp X Y ((ihom PointedSimplicialSet.circle.{u}).obj Z) ≫
      ihomUncurry PointedSimplicialSet.circle.{u} X Z =
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map PointedSimplicialSet.circle.{u} X Y ⊗ₘ
      ihomUncurry PointedSimplicialSet.circle.{u} Y Z) ≫
      MonoidalClosed.comp (PointedSimplicialSet.circle.{u} ⊗ X)
        (PointedSimplicialSet.circle.{u} ⊗ Y) Z
  apply uncurry_injective
  simp only [uncurry_natural_left, uncurry_ihomUncurry, comp_eq, uncurry_curry,
    compTranspose_eq]
  conv_lhs =>
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc,
      whiskerLeft_curry_ihom_ev_app]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [tensorHom_def, whiskerLeft_comp]
  simp only [Category.assoc]
  rw [associator_inv_naturality_right_assoc,
    associator_inv_naturality_middle_assoc]
  rw [whisker_exchange_assoc,
    ← comp_whiskerRight_assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.evaluation]
  have hev : (PointedSimplicialSet.circle.{u} ⊗ Y) ◁
      ihomUncurry PointedSimplicialSet.circle.{u} Y Z ≫
        (ihom.ev (PointedSimplicialSet.circle.{u} ⊗ Y)).app Z =
    (α_ PointedSimplicialSet.circle.{u} Y _).hom ≫
      PointedSimplicialSet.circle.{u} ◁ (ihom.ev Y).app
        ((ihom PointedSimplicialSet.circle.{u}).obj Z) ≫
          (ihom.ev PointedSimplicialSet.circle.{u}).app Z :=
    uncurry_ihomUncurry PointedSimplicialSet.circle.{u} Y Z
  dsimp only [Functor.id_obj]
  rw [hev]
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_naturality_middle_assoc]
  rw [pentagon_inv_hom_hom_hom_inv_assoc]

/-- 順随伴も入力射の豊穣前合成を保つ。 -/
lemma suspensionLoopPointedMappingIso_enriched_pre
    (X Y Z : PointedSimplicialSet.{u}) :
    (suspensionHom X Y ⊗ₘ 𝟙 (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y) Z)) ≫
        MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y) Z ≫
          (suspensionLoopPointedMappingIso X Z).hom =
      (𝟙 (PointedObject.basedHom X Y) ⊗ₘ (suspensionLoopPointedMappingIso Y Z).hom) ≫
        MonoidalClosed.comp X Y (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z) := by
  apply (cancel_mono (suspensionLoopPointedMappingIso X Z).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [suspensionLoopPointedMappingIso_inv_enriched_pre,
    ← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Category.id_comp, Iso.hom_inv_id]

/-- 基点固定写像空間の単体的合成は、逆随伴による移送と厳密に可換。 -/
lemma suspensionLoopMappingIso_inv_enriched_pre
    (X Y Z : PointedSimplicialSet.{u}) :
    pointedMappingComposition X Y (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z) ≫ (suspensionLoopMappingIso X Z).inv =
      ((suspensionHom X Y).right ⊗ₘ (suspensionLoopMappingIso Y Z).inv) ≫
        pointedMappingComposition (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y) Z := by
  change PointedSimplicialSet.productToSmash _ _ ≫
      (MonoidalClosed.comp X Y (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z)).right ≫
        (suspensionLoopPointedMappingIso X Z).inv.right =
    ((suspensionHom X Y).right ⊗ₘ (suspensionLoopPointedMappingIso Y Z).inv.right) ≫
      PointedSimplicialSet.productToSmash _ _ ≫
        (MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y) Z).right
  rw [← Under.comp_right, suspensionLoopPointedMappingIso_inv_enriched_pre,
    Under.comp_right, ← Category.assoc, ← PointedSimplicialSet.productToSmash_naturality,
    Category.assoc]

/-- 独立な二つの単体パラメータを持つ前合成の族を、同時に suspension 側へ移す。 -/
lemma suspensionLoopMappingFamilies_inv_pre {P Q : SSet.{u}}
    {X Y Z : PointedSimplicialSet.{u}}
    (a : P ⟶ (PointedObject.basedHom X Y).right)
    (b : Q ⟶ (PointedObject.basedHom Y (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z)).right) :
    (a ⊗ₘ b) ≫ pointedMappingComposition X Y (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z) ≫
        (suspensionLoopMappingIso X Z).inv =
      ((a ≫ (suspensionHom X Y).right) ⊗ₘ (b ≫ (suspensionLoopMappingIso Y Z).inv)) ≫
        pointedMappingComposition (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y) Z := by
  rw [suspensionLoopMappingIso_inv_enriched_pre,
    ← Category.assoc, ← tensorHom_comp_tensorHom]

end SerrePositivity.KST.SConstruction
