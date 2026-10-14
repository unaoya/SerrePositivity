module

public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorFreeRight

/-! # 二つの自由加群の釣り合いテンソル積 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (M : C) [MonObj M]

/-- 自由加群の右テンソルを、生成対象のテンソルから作る自由加群へ比較する。 -/
def freeTensorIso (X Y : C) :
    tensorRightObj M (MonoidalFreeModule.freeObj M X) Y ≅
      MonoidalFreeModule.freeObj M (X ⊗ Y) := by
  let h : tensorRightObj M (MonoidalFreeModule.freeObj M X) Y ⟶
      MonoidalFreeModule.freeObj M (X ⊗ Y) :=
    tensorRightAssociator M (Mod.regular M) X Y
  letI : ModObj M ((M ⊗ X) ⊗ Y) :=
    tensorRightAction M (MonoidalFreeModule.freeObj M X) Y
  letI : ModObj M (M ⊗ (X ⊗ Y)) := MonoidalFreeModule.freeAction M (X ⊗ Y)
  have : IsModHom M (α_ M X Y).hom := h.isModHom
  have : IsModHom M (α_ M X Y).inv := inferInstance
  exact {
    hom := h
    inv := Mod.Hom.mk' (α_ M X Y).inv IsModHom.smul_hom
    hom_inv_id := Mod.hom_ext _ _ (α_ M X Y).hom_inv_id
    inv_hom_id := Mod.hom_ext _ _ (α_ M X Y).inv_hom_id }

/-- 自由加群の右テンソルの比較の順方向は基礎圏の結合子。 -/
lemma freeTensorIso_hom (X Y : C) : (freeTensorIso M X Y).hom.hom = (α_ M X Y).hom := rfl

/-- 自由加群の右テンソルの比較の逆方向は基礎圏の結合子の逆。 -/
lemma freeTensorIso_inv (X Y : C) : (freeTensorIso M X Y).inv.hom = (α_ M X Y).inv := rfl

/-- 自由加群の右テンソルの比較は両方の生成対象に関して自然。 -/
lemma freeTensor_naturality {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorRightMap M (MonoidalFreeModule.freeMap M f) g ≫ (freeTensorIso M X' Y').hom =
      (freeTensorIso M X Y).hom ≫ MonoidalFreeModule.freeMap M (f ⊗ₘ g) := by
  apply Mod.hom_ext
  change ((M ◁ f) ⊗ₘ g) ≫ (α_ M X' Y').hom =
    (α_ M X Y).hom ≫ M ◁ (f ⊗ₘ g)
  simp only [tensorHom_def, whiskerLeft_comp, Category.assoc]
  rw [associator_naturality_right, associator_naturality_middle_assoc]

/-- 自由加群の生成元は結合子を介して右テンソルの生成元と一致する。 -/
@[reassoc] lemma generator_associator_inv (X Y : C) :
    MonoidalFreeModule.generator M (X ⊗ Y) ≫ (α_ M X Y).inv =
      MonoidalFreeModule.generator M X ▷ Y := by
  simp only [MonoidalFreeModule.generator, Category.assoc]
  change (λ_ (X ⊗ Y)).inv ≫ η[M] ▷ (X ⊗ Y) ≫ (α_ M X Y).inv =
    ((λ_ X).inv ≫ η[M] ▷ X) ▷ Y
  rw [associator_inv_naturality_left, comp_whiskerRight]
  have h : (λ_ (X ⊗ Y)).inv ≫ (α_ (𝟙_ C) X Y).inv = (λ_ X).inv ▷ Y := by monoidal
  rw [← Category.assoc, h]

variable [BraidedCategory C] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]

/-- 二つの自由加群の釣り合いテンソル積は、生成対象の積から作る自由加群と同型。 -/
def freePairIso (X Y : C) :
    moduleObj M (MonoidalFreeModule.freeObj M X) (MonoidalFreeModule.freeObj M Y) ≅
      MonoidalFreeModule.freeObj M (X ⊗ Y) :=
  freeRightIso M (MonoidalFreeModule.freeObj M X) Y ≪≫ freeTensorIso M X Y

/-- 二つの自由加群の比較は両方の生成対象の射に関して自然。 -/
lemma freePair_naturality {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    moduleMap M (MonoidalFreeModule.freeMap M f) (MonoidalFreeModule.freeMap M g) ≫
        (freePairIso M X' Y').hom =
      (freePairIso M X Y).hom ≫ MonoidalFreeModule.freeMap M (f ⊗ₘ g) := by
  change moduleMap M (MonoidalFreeModule.freeMap M f) (MonoidalFreeModule.freeMap M g) ≫
      (freeRightIso M (MonoidalFreeModule.freeObj M X') Y').hom ≫
        (freeTensorIso M X' Y').hom =
    ((freeRightIso M (MonoidalFreeModule.freeObj M X) Y).hom ≫
      (freeTensorIso M X Y).hom) ≫ MonoidalFreeModule.freeMap M (f ⊗ₘ g)
  rw [← Category.assoc, freeRight_naturality, Category.assoc, freeTensor_naturality,
    Category.assoc]

/-- 逆比較は自由加群の生成元を二つの生成元のテンソルへ送る。 -/
@[reassoc] lemma generator_freePair_inv (X Y : C) :
    MonoidalFreeModule.generator M (X ⊗ Y) ≫ (freePairIso M X Y).inv.hom =
      (MonoidalFreeModule.generator M X ⊗ₘ MonoidalFreeModule.generator M Y) ≫
        projection M (MonoidalFreeModule.freeObj M X) (MonoidalFreeModule.freeObj M Y) := by
  change MonoidalFreeModule.generator M (X ⊗ Y) ≫ (α_ M X Y).inv ≫
      (M ⊗ X) ◁ MonoidalFreeModule.generator M Y ≫
        projection M (MonoidalFreeModule.freeObj M X) (MonoidalFreeModule.freeObj M Y) = _
  rw [generator_associator_inv_assoc]
  simp only [tensorHom_def, Category.assoc, MonoidalFreeModule.freeObj]

/-- 順比較は二つの生成元のテンソルを、積から作る自由加群の生成元へ送る。 -/
@[reassoc] lemma generators_freePair_hom (X Y : C) :
    (MonoidalFreeModule.generator M X ⊗ₘ MonoidalFreeModule.generator M Y) ≫
        projection M (MonoidalFreeModule.freeObj M X) (MonoidalFreeModule.freeObj M Y) ≫
          (freePairIso M X Y).hom.hom = MonoidalFreeModule.generator M (X ⊗ Y) := by
  rw [← generator_freePair_inv_assoc]
  have h := congrArg Mod.Hom.hom (freePairIso M X Y).inv_hom_id
  change (freePairIso M X Y).inv.hom ≫ (freePairIso M X Y).hom.hom = 𝟙 _ at h
  rw [h, Category.comp_id]

/-- 二つの自由加群を釣り合いテンソルする二変数関手。 -/
def freePairBifunctor : C × C ⥤ Mod C M :=
  (MonoidalFreeModule.freeFunctor M).prod (MonoidalFreeModule.freeFunctor M) ⋙
    moduleBifunctor M

/-- 生成対象をテンソルして自由加群を作る二変数関手。 -/
def freeProductBifunctor : C × C ⥤ Mod C M := tensor C ⋙ MonoidalFreeModule.freeFunctor M

/-- 二つの自由加群の釣り合いテンソル積の二変数の自然比較。 -/
def freePairNatIso : freePairBifunctor M ≅ freeProductBifunctor M :=
  NatIso.ofComponents (fun XY => freePairIso M XY.1 XY.2)
    (fun fg => freePair_naturality M fg.1 fg.2)

end SerrePositivity.MonoidalBalancedTensor
