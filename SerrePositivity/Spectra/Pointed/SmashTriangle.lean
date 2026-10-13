module

public import SerrePositivity.Spectra.Pointed.SmashAssociator
public import SerrePositivity.Spectra.Pointed.SmashUnit

/-!
# smash 積の triangle

零次球面の二成分に沿って単位と結合を比較する。
非基点側では恒等射、基点側では smash の軸の零化へ帰着する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.PointedObject

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [MonoidalClosed C] [HasFiniteColimits C]

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory

/-- 左単位の raw map は、非基点側に任意の射を入れるとその射を返す。 -/
@[reassoc (attr := simp)] lemma leftUnitRaw_inl {T : C} (X : PointedObject C)
    (f : T ⟶ X.right) :
    lift (toUnit T ≫ (coprod.inl : 𝟙_ C ⟶ 𝟙_ C ⨿ 𝟙_ C)) f ≫ leftUnitRaw X = f := by
  have h : lift (toUnit T ≫ (coprod.inl : 𝟙_ C ⟶ 𝟙_ C ⨿ 𝟙_ C)) f =
      lift (toUnit T) f ≫ (coprod.inl ▷ X.right) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [h, Category.assoc, leftUnitRaw_first]
  simp

/-- 基点側に任意の射を入れると、行き先の基点で定数となる。 -/
@[reassoc (attr := simp)] lemma leftUnitRaw_inr {T : C} (X : PointedObject C)
    (f : T ⟶ X.right) :
    lift (toUnit T ≫ (coprod.inr : 𝟙_ C ⟶ 𝟙_ C ⨿ 𝟙_ C)) f ≫ leftUnitRaw X =
      toUnit T ≫ X.hom := by
  have h : lift (toUnit T ≫ (coprod.inr : 𝟙_ C ⟶ 𝟙_ C ⨿ 𝟙_ C)) f =
      lift (toUnit T) f ≫ (coprod.inr ▷ X.right) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [h, Category.assoc, leftUnitRaw_second]
  simp

/-- 三変数の中央に零次球面の指定された成分を挿入する基礎圏の射。 -/
def middleUnitSeed (X Y : PointedObject C) (j : 𝟙_ C ⟶ (𝟙_ C ⨿ 𝟙_ C)) :
    (prod X Y).right ⟶ (prod (prod X sphereZero) Y).right :=
  lift (lift (fst X.right Y.right) (toUnit (prod X Y).right ≫ j)) (snd X.right Y.right)

omit [MonoidalClosed C] in
/-- sphere を先頭から中央へ移すと、二成分の挿入を比較できる。 -/
@[reassoc] lemma middleUnitSeed_component (X Y : PointedObject C)
    (j : 𝟙_ C ⟶ (𝟙_ C ⨿ 𝟙_ C)) :
    (j ▷ (X.right ⊗ Y.right)) ≫ (α_ sphereZero.right X.right Y.right).inv ≫
      ((β_ sphereZero.right X.right).hom ▷ Y.right) =
    (λ_ (X.right ⊗ Y.right)).hom ≫ middleUnitSeed X Y j := by
  dsimp [middleUnitSeed, prod, sphereZero, adjoin]
  apply CartesianMonoidalCategory.hom_ext
  · apply CartesianMonoidalCategory.hom_ext <;>
      simp [Category.assoc, CartesianMonoidalCategory.leftUnitor_hom]
  · simp [Category.assoc, CartesianMonoidalCategory.leftUnitor_hom]

/-- smash の結合射は左右単位と triangle を満たす。 -/
lemma smashAssoc_triangle (X Y : PointedObject C) :
    smashAssocHom X sphereZero Y ≫ smashMap (𝟙 X) (leftUnitHom Y) =
      smashMap (smashRightUnitor X).hom (𝟙 Y) := by
  apply (cancel_epi (leftTripleQuotient X sphereZero Y)).mp
  rw [leftTripleQuotient_assocHom_assoc]
  simp only [rightTripleQuotient, leftTripleQuotient, Category.assoc, smashQuotient_map]
  simp only [← Category.assoc, prodMap_comp, Category.comp_id,
    smashQuotient_leftUnitHom]
  have hr : smashQuotient X sphereZero ≫ (smashRightUnitor X).hom =
      prodSwap X sphereZero ≫ leftUnitProduct X := by
    change smashQuotient X sphereZero ≫
      (smashSwap X sphereZero ≫ leftUnitHom X) = _
    simp
  rw [hr]
  apply Under.UnderMorphism.ext
  apply (cancel_epi ((α_ sphereZero.right X.right Y.right).inv ≫
    ((β_ sphereZero.right X.right).hom ▷ Y.right))).mp
  simp only [Category.assoc]
  apply tensorRightCoprod_hom_ext
  · rw [middleUnitSeed_component_assoc, middleUnitSeed_component_assoc]
    simp only [Under.comp_right, Under.id_right, prodMap_right,
      leftUnitProduct, Under.homMk_right]
    simp [middleUnitSeed, prodAssocHom, prodSwap, prodLift, prodFst, prodSnd,
      prod, sphereZero, adjoin, Category.assoc]
    simp [← Category.assoc]
  · rw [middleUnitSeed_component_assoc, middleUnitSeed_component_assoc]
    simp only [Under.comp_right, Under.id_right, prodMap_right,
      leftUnitProduct, Under.homMk_right]
    simp only [sphereZero, adjoin, Under.mk_right, middleUnitSeed, prod, Under.mk_hom,
      prodAssocHom, prodLift, prodFst, Under.comp_right, Under.homMk_right, prodSnd,
      id_tensorHom, lift_whiskerLeft_assoc, prodSwap, tensorHom_id, comp_whiskerRight,
      Category.assoc, lift_whiskerRight_assoc, comp_lift, lift_snd, lift_fst,
      leftUnitRaw_inr, Iso.cancel_iso_hom_left]
    simp only [← Category.assoc, comp_lift, lift_fst, lift_snd, leftUnitRaw_inr]
    have hl := congrArg (fun k ↦ (prodFst X Y).right ≫ k)
      (congrArg Under.Hom.right (axisLeft_smashQuotient X Y))
    have hr := congrArg (fun k ↦ (prodSnd X Y).right ≫ k)
      (congrArg Under.Hom.right (axisRight_smashQuotient X Y))
    simp [Under.comp_right, axisLeft, axisRight, prodLift, zero_right,
      prodFst, prodSnd] at hl hr
    simp [← Category.assoc] at hl hr
    exact hl.trans hr.symm

end SerrePositivity.PointedObject
