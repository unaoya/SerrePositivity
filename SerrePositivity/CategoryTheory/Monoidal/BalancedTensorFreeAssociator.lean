module

public import SerrePositivity.CategoryTheory.Monoidal.FreeModuleMonoidal
public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorFreeLeft

/-! # 二つの左自由因子の結同比較と基礎圏の結合子 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped CategoryTheory.MonObj
open MonoidalFreeModule

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  (M : C) [MonObj M] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

/-- 二つの左自由因子を通常のテンソルへ比較した結合同型。 -/
def freeLeftPairAssociator (X Y : C) (A : Mod C M) :
    tensorLeftObj M (X ⊗ Y) A ≅ tensorLeftObj M X (tensorLeftObj M Y A) :=
  (freeLeftIso M (X ⊗ Y) A).symm ≪≫ tensorIso (freePairIso M X Y).symm (Iso.refl A) ≪≫
    α_ (freeObj M X) (freeObj M Y) A ≪≫
      (tensorLeft (freeObj M X)).mapIso (freeLeftIso M Y A) ≪≫
        freeLeftIso M X (tensorLeftObj M Y A)

/-- 自由因子の結同比較の基礎射は通常の結合子。 -/
lemma freeLeftPairAssociator_hom (X Y : C) (A : Mod C M) :
    (freeLeftPairAssociator M X Y A).hom.hom = (α_ X Y A.X).hom := by
  unfold freeLeftPairAssociator
  simp only [Iso.trans_hom, Mod.comp_hom']
  change (freeLeftIso M (X ⊗ Y) A).inv.hom ≫
    map M (freePairIso M X Y).inv (𝟙 A) ≫ associatorHom M (freeObj M X) (freeObj M Y) A ≫
      map M (𝟙 (freeObj M X)) (freeLeftIso M Y A).hom ≫
        (freeLeftIso M X (tensorLeftObj M Y A)).hom.hom = _
  rw [freeLeftIso_inv, Category.assoc, projection_map_assoc, Mod.id_hom', tensorHom_id]
  rw [← comp_whiskerRight_assoc, generator_freePair_inv, comp_whiskerRight]
  simp only [Category.assoc]
  have ht := tripleLeftProjection_associatorHom M (freeObj M X) (freeObj M Y) A
  unfold tripleLeftProjection at ht
  simp only [Category.assoc] at ht
  rw [reassoc_of% ht, tripleRightProjection]
  simp only [Category.assoc]
  rw [projection_map_assoc, Mod.id_hom', id_tensorHom]
  have ha := CategoryTheory.MonoidalCategory.associator_naturality
    (generator M X) (generator M Y) (𝟙 A.X)
  rw [tensorHom_id, tensorHom_id] at ha
  rw [tensorHom_def (generator M X) (generator M Y ▷ A.X)] at ha
  rw [reassoc_of% ha]
  rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  erw [generator_freeLeft_hom, whiskerLeft_id, Category.id_comp,
    generator_freeLeft_hom M X (tensorLeftObj M Y A), Category.comp_id]

/-- 自由因子の結同比較の逆射も通常の逆結合子。 -/
lemma freeLeftPairAssociator_inv (X Y : C) (A : Mod C M) :
    (freeLeftPairAssociator M X Y A).inv.hom = (α_ X Y A.X).inv := by
  apply (cancel_mono (α_ X Y A.X).hom).mp
  calc
    _ = (freeLeftPairAssociator M X Y A).inv.hom ≫
        (freeLeftPairAssociator M X Y A).hom.hom :=
      congrArg (fun f => (freeLeftPairAssociator M X Y A).inv.hom ≫ f)
        (freeLeftPairAssociator_hom M X Y A).symm
    _ = 𝟙 _ := congrArg Mod.Hom.hom (freeLeftPairAssociator M X Y A).inv_hom_id
    _ = _ := (α_ X Y A.X).inv_hom_id.symm

/-- 左自由因子の逆比較の両変数の自然性。 -/
lemma freeLeft_inv_naturality {X Y : C} (g : X ⟶ Y) {A B : Mod C M} (f : A ⟶ B) :
    (freeLeftIso M X A).inv ≫ (freeMap M g ⊗ₘ f) =
      tensorLeftMap M g f ≫ (freeLeftIso M Y B).inv := by
  apply (cancel_mono (freeLeftIso M Y B).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (freeLeftIso M X A).inv ≫
    moduleMap M (freeMap M g) f ≫ (freeLeftIso M Y B).hom = _
  rw [freeLeft_naturality, Iso.inv_hom_id_assoc]

/-- 自由生成の射と値域への比較を含む結同比較を左自由因子の比較へ分解する。 -/
lemma freeLeftPairAssociator_transport {Z X Y : C} (g : Z ⟶ X ⊗ Y)
    (A B : Mod C M) (h : tensorLeftObj M Y A ⟶ B) :
    (freeLeftIso M Z A).inv ≫ freeMap M g ▷ A ≫
      (freePairIso M X Y).inv ▷ A ≫ (α_ (freeObj M X) (freeObj M Y) A).hom ≫
        freeObj M X ◁ ((freeLeftIso M Y A).hom ≫ h) ≫ (freeLeftIso M X B).hom =
    tensorLeftMap M g (𝟙 A) ≫ (freeLeftPairAssociator M X Y A).hom ≫
      tensorLeftMap M (𝟙 X) h := by
  have hg := freeLeft_inv_naturality M g (𝟙 A)
  rw [tensorHom_id] at hg
  have hh := freeLeft_naturality M (𝟙 X) h
  have hi : freeMap M (𝟙 X) = 𝟙 (freeObj M X) := (freeFunctor M).map_id X
  rw [hi] at hh
  change (freeObj M X ◁ h) ≫ (freeLeftIso M X B).hom =
    (freeLeftIso M X (tensorLeftObj M Y A)).hom ≫ tensorLeftMap M (𝟙 X) h at hh
  rw [← Category.assoc, hg]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [hh]
  simp only [freeLeftPairAssociator, Iso.trans_hom, tensorIso_hom,
    Iso.symm_hom, Iso.refl_hom, tensorHom_id, Category.assoc]
  rfl

end SerrePositivity.MonoidalBalancedTensor
