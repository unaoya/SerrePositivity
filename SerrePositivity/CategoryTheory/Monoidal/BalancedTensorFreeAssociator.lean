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

end SerrePositivity.MonoidalBalancedTensor
