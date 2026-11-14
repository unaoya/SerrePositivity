module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.CategoryTheory.Monoidal.Mod.Monoidal
public import SerrePositivity.CategoryTheory.Monoidal.Mod.Free
public import SerrePositivity.CategoryTheory.Monoidal.Mod.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Monoidal.Mod.FreeTensor

## 概要
関連する圏論の構成と補題をまとめる。各構成の詳細は以下の元モジュールの説明を参照。

## 方針
元の宣言と証明を保持し、依存順に section を分けて配置する。

## 規約
公開宣言名・名前空間・宇宙変数の意味を変更しない。元の module docstring は各節に保存する。

## 使われ方
旧モジュールの利用元は `SerrePositivity.CategoryTheory.Monoidal.Mod.FreeTensor` を直接 import する。
-/

/-! ## BalancedTensorFreeRight（旧 SerrePositivity/CategoryTheory/Monoidal/BalancedTensorFreeRight.lean） -/

/-! # 自由加群を右因子とする釣り合いテンソル積 -/

@[expose] public section BalancedTensorFreeRight
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (M : C) [MonObj M] [IsCommMonObj M] [HasCoequalizers C]

/-- 自由加群の係数を第一因子の右作用へ移す射。 -/
def freeRightBalanced (E : Mod C M) (X : C) :
    BalancedMap M E (MonoidalFreeModule.freeObj M X) (E.X ⊗ X) :=
  ⟨(α_ E.X M X).inv ≫ rightActionMap M E ▷ X, by
    change rightActionMap M E ▷ (M ⊗ X) ≫
        ((α_ E.X M X).inv ≫ rightActionMap M E ▷ X) =
      ((α_ E.X M (M ⊗ X)).hom ≫
        E.X ◁ ((α_ M M X).inv ≫ μ[M] ▷ X)) ≫
          ((α_ E.X M X).inv ≫ rightActionMap M E ▷ X)
    simp only [Category.assoc, whiskerLeft_comp]
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight,
      rightActionMap_assoc, comp_whiskerRight, comp_whiskerRight]
    rw [associator_inv_naturality_middle_assoc]
    have h : (α_ (E.X ⊗ M) M X).inv ≫ (α_ E.X M M).hom ▷ X =
        (α_ E.X M (M ⊗ X)).hom ≫ E.X ◁ (α_ M M X).inv ≫
          (α_ E.X (M ⊗ M) X).inv := by monoidal
    simpa only [Category.assoc] using
      congrArg (fun k => k ≫ (E.X ◁ μ[M]) ▷ X ≫ rightActionMap M E ▷ X) h⟩

/-- 自由加群との釣り合い商から通常の右テンソルへの比較射。 -/
def freeRightHom (E : Mod C M) (X : C) :
    obj M E (MonoidalFreeModule.freeObj M X) ⟶ E.X ⊗ X :=
  desc M (freeRightBalanced M E X)

/-- 自由加群の生成元を挿入する逆比較射。 -/
def freeRightInv (E : Mod C M) (X : C) :
    E.X ⊗ X ⟶ obj M E (MonoidalFreeModule.freeObj M X) :=
  E.X ◁ MonoidalFreeModule.generator M X ≫
    projection M E (MonoidalFreeModule.freeObj M X)

/-- 比較射は標準射上で係数の右作用に一致する。 -/
@[reassoc (attr := simp)] lemma projection_freeRightHom (E : Mod C M) (X : C) :
    projection M E (MonoidalFreeModule.freeObj M X) ≫ freeRightHom M E X =
      (α_ E.X M X).inv ≫ rightActionMap M E ▷ X := projection_desc M _

/-- 生成元を挿入して係数を作用させると恒等射になる。 -/
lemma freeRightInv_hom (E : Mod C M) (X : C) :
    freeRightInv M E X ≫ freeRightHom M E X = 𝟙 (E.X ⊗ X) := by
  rw [freeRightInv, Category.assoc, projection_freeRightHom]
  change E.X ◁ ((λ_ X).inv ≫ η[M] ▷ X) ≫
    (α_ E.X M X).inv ≫ rightActionMap M E ▷ X = _
  rw [whiskerLeft_comp, Category.assoc, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight, rightActionMap_one]
  monoidal

/-- 係数を作用させて生成元を挿入すると商上の恒等射になる。 -/
lemma freeRightHom_inv (E : Mod C M) (X : C) :
    freeRightHom M E X ≫ freeRightInv M E X =
      𝟙 (obj M E (MonoidalFreeModule.freeObj M X)) := by
  apply hom_ext M
  rw [projection_freeRightHom_assoc, freeRightInv]
  slice_lhs 2 3 => rw [← whisker_exchange]
  have hc := projection_condition M E (MonoidalFreeModule.freeObj M X)
  change rightActionMap M E ▷ (M ⊗ X) ≫ projection M E (MonoidalFreeModule.freeObj M X) =
    ((α_ E.X M (M ⊗ X)).hom ≫ E.X ◁ γ[M,(MonoidalFreeModule.freeObj M X).X]) ≫
      projection M E (MonoidalFreeModule.freeObj M X) at hc
  slice_lhs 3 4 => erw [hc]
  simp only [Category.assoc]
  slice_lhs 2 3 => erw [associator_naturality_right]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc,
    MonoidalFreeModule.generator_action, whiskerLeft_id, Category.id_comp, Category.comp_id]

/-- 自由加群との右釣り合いテンソル積の基礎対象の比較同型。 -/
def freeRightUnderlyingIso (E : Mod C M) (X : C) :
    obj M E (MonoidalFreeModule.freeObj M X) ≅ E.X ⊗ X where
  hom := freeRightHom M E X
  inv := freeRightInv M E X
  hom_inv_id := freeRightHom_inv M E X
  inv_hom_id := freeRightInv_hom M E X

variable [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]

/-- 係数を右作用へ移す比較射は加群作用と両立する。 -/
def freeRightModuleHom (E : Mod C M) (X : C) :
    moduleObj M E (MonoidalFreeModule.freeObj M X) ⟶ tensorRightObj M E X :=
  moduleDesc M (freeRightBalanced M E X) (by
    change (α_ M E.X (M ⊗ X)).inv ≫ γ[M,E.X] ▷ (M ⊗ X) ≫
        (α_ E.X M X).inv ≫ rightActionMap M E ▷ X =
      M ◁ ((α_ E.X M X).inv ≫ rightActionMap M E ▷ X) ≫
        (α_ M E.X X).inv ≫ γ[M,E.X] ▷ X
    let : ModObj M (E.X ⊗ (M ⊗ X)) := tensorRightAction M E (M ⊗ X)
    let : ModObj M ((E.X ⊗ M) ⊗ X) := tensorRightAction M (tensorRightObj M E M) X
    have : IsModHom M (α_ E.X M X).hom :=
      (tensorRightAssociator M E M X).isModHom
    have : IsModHom M (α_ E.X M X).inv := inferInstance
    let a : tensorRightObj M E (M ⊗ X) ⟶
        tensorRightObj M (tensorRightObj M E M) X :=
      Mod.Hom.mk' (α_ E.X M X).inv IsModHom.smul_hom
    let f := a ≫ tensorRightMap M (rightActionHom M E) (𝟙 X)
    have h := IsModHom.smul_hom (A := M) (f := f.hom)
    change ((α_ M E.X (M ⊗ X)).inv ≫ γ[M,E.X] ▷ (M ⊗ X)) ≫
        ((α_ E.X M X).inv ≫ (rightActionMap M E ⊗ₘ 𝟙 X)) =
      M ◁ ((α_ E.X M X).inv ≫ (rightActionMap M E ⊗ₘ 𝟙 X)) ≫
        ((α_ M E.X X).inv ≫ γ[M,E.X] ▷ X) at h
    simpa only [tensorHom_id, Category.assoc] using h)

/-- 自由加群との右テンソル積を通常の右テンソルへ比較する加群同型。 -/
def freeRightIso (E : Mod C M) (X : C) :
    moduleObj M E (MonoidalFreeModule.freeObj M X) ≅ tensorRightObj M E X := by
  let i := freeRightUnderlyingIso M E X
  letI : ModObj M (obj M E (MonoidalFreeModule.freeObj M X)) :=
    (moduleObj M E (MonoidalFreeModule.freeObj M X)).mod
  letI := tensorRightAction M E X
  have : IsModHom M i.hom := (freeRightModuleHom M E X).isModHom
  have : IsModHom M i.inv := inferInstance
  exact {
    hom := freeRightModuleHom M E X
    inv := Mod.Hom.mk' i.inv IsModHom.smul_hom
    hom_inv_id := Mod.hom_ext _ _ i.hom_inv_id
    inv_hom_id := Mod.hom_ext _ _ i.inv_hom_id }

/-- 自由加群との比較同型の順方向の基礎射。 -/
lemma freeRightIso_hom (E : Mod C M) (X : C) :
    (freeRightIso M E X).hom.hom = freeRightHom M E X := rfl

/-- 自由加群との比較同型の逆方向の基礎射。 -/
lemma freeRightIso_inv (E : Mod C M) (X : C) :
    (freeRightIso M E X).inv.hom = freeRightInv M E X := rfl

/-- 自由加群との比較は加群と生成対象の両方に関して自然。 -/
lemma freeRight_naturality {E E' : Mod C M} (f : E ⟶ E') {X Y : C} (g : X ⟶ Y) :
    moduleMap M f (MonoidalFreeModule.freeMap M g) ≫ (freeRightIso M E' Y).hom =
      (freeRightIso M E X).hom ≫ tensorRightMap M f g := by
  apply Mod.hom_ext
  apply hom_ext M
  change projection M E (MonoidalFreeModule.freeObj M X) ≫
      map M f (MonoidalFreeModule.freeMap M g) ≫ freeRightHom M E' Y =
    projection M E (MonoidalFreeModule.freeObj M X) ≫ freeRightHom M E X ≫ (f.hom ⊗ₘ g)
  rw [projection_map_assoc, projection_freeRightHom, projection_freeRightHom_assoc]
  change (f.hom ⊗ₘ M ◁ g) ≫ (α_ E'.X M Y).inv ≫ rightActionMap M E' ▷ Y =
    (α_ E.X M X).inv ≫ rightActionMap M E ▷ X ≫ (f.hom ⊗ₘ g)
  simp only [tensorHom_def, Category.assoc]
  rw [associator_inv_naturality_right_assoc, associator_inv_naturality_left_assoc]
  slice_lhs 3 4 => rw [whisker_exchange]
  slice_lhs 2 3 => rw [← comp_whiskerRight, ← rightActionMap_naturality]
  simp only [comp_whiskerRight, Category.assoc]

/-- 加群の右に対象をテンソルする二変数関手。 -/
def tensorRightBifunctor : Mod C M × C ⥤ Mod C M where
  obj EX := tensorRightObj M EX.1 EX.2
  map fg := tensorRightMap M fg.1 fg.2
  map_id EX := by
    apply Mod.hom_ext
    change (𝟙 EX.1.X ⊗ₘ 𝟙 EX.2) = 𝟙 (EX.1.X ⊗ EX.2)
    simp
  map_comp fg gh := by
    apply Mod.hom_ext
    change (fg.1.hom ≫ gh.1.hom) ⊗ₘ (fg.2 ≫ gh.2) =
      (fg.1.hom ⊗ₘ fg.2) ≫ (gh.1.hom ⊗ₘ gh.2)
    simp only [tensorHom_comp_tensorHom]

/-- 第二因子を自由加群にした釣り合いテンソル積の二変数関手。 -/
def freeRightBifunctor : Mod C M × C ⥤ Mod C M :=
  (𝟭 (Mod C M)).prod (MonoidalFreeModule.freeFunctor M) ⋙ moduleBifunctor M

/-- 自由加群との釣り合いテンソル積を通常の右テンソルへ比較する自然同型。 -/
def freeRightNatIso : freeRightBifunctor M ≅ tensorRightBifunctor M :=
  NatIso.ofComponents (fun EX => freeRightIso M EX.1 EX.2)
    (fun fg => freeRight_naturality M fg.1 fg.2)

end SerrePositivity.MonoidalBalancedTensor
end

end BalancedTensorFreeRight

/-! ## BalancedTensorFreeLeft（旧 SerrePositivity/CategoryTheory/Monoidal/BalancedTensorFreeLeft.lean） -/

/-! # 自由加群を左因子とする釣り合いテンソル積 -/

@[expose] public section BalancedTensorFreeLeft
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  (M : C) [MonObj M]

/-- 右テンソルの作用を交換同型で左テンソルへ移す。 -/
@[instance_reducible] def tensorLeftAction (X : C) (E : Mod C M) : ModObj M (X ⊗ E.X) := by
  letI := tensorRightAction M E X
  have : IsMonHom (Iso.refl M).hom := inferInstanceAs (IsMonHom (𝟙 M))
  exact ModObj.ofIso (Iso.refl M) (β_ E.X X)

/-- 対象を加群の左にテンソルし、交換で移した作用を与える。 -/
def tensorLeftObj (X : C) (E : Mod C M) : Mod C M :=
  letI := tensorLeftAction M X E
  ⟨X ⊗ E.X⟩

/-- 左に移したテンソルの作用の具体式。 -/
lemma tensorLeftObj_action (X : C) (E : Mod C M) :
    γ[M,(tensorLeftObj M X E).X] = M ◁ (β_ E.X X).inv ≫
      (α_ M E.X X).inv ≫ γ[M,E.X] ▷ X ≫ (β_ E.X X).hom := by
  change (𝟙 M ⊗ₘ (β_ E.X X).inv) ≫
    ((α_ M E.X X).inv ≫ γ[M,E.X] ▷ X) ≫ (β_ E.X X).hom = _
  rw [id_tensorHom, Category.assoc]

/-- 加群の左右の通常のテンソルを比較する交換同型。 -/
def tensorLeftIso (E : Mod C M) (X : C) : tensorRightObj M E X ≅ tensorLeftObj M X E := by
  letI : ModObj M (E.X ⊗ X) := tensorRightAction M E X
  letI : ModObj M (X ⊗ E.X) := tensorLeftAction M X E
  have : IsModHom M (β_ E.X X).hom := ⟨by
    change ((α_ M E.X X).inv ≫ γ[M,E.X] ▷ X) ≫ (β_ E.X X).hom =
      M ◁ (β_ E.X X).hom ≫ ((𝟙 M ⊗ₘ (β_ E.X X).inv) ≫
        ((α_ M E.X X).inv ≫ γ[M,E.X] ▷ X) ≫ (β_ E.X X).hom)
    rw [id_tensorHom]
    simp only [Category.assoc, ← whiskerLeft_comp_assoc, Iso.hom_inv_id,
      whiskerLeft_id, Category.id_comp]⟩
  have : IsModHom M (β_ E.X X).inv := inferInstance
  exact {
    hom := Mod.Hom.mk' (β_ E.X X).hom IsModHom.smul_hom
    inv := Mod.Hom.mk' (β_ E.X X).inv IsModHom.smul_hom
    hom_inv_id := Mod.hom_ext _ _ (β_ E.X X).hom_inv_id
    inv_hom_id := Mod.hom_ext _ _ (β_ E.X X).inv_hom_id }

/-- 左テンソルの射を、右テンソルの射と交換同型から構成する。 -/
def tensorLeftMap {X Y : C} (g : X ⟶ Y) {E E' : Mod C M} (f : E ⟶ E') :
    tensorLeftObj M X E ⟶ tensorLeftObj M Y E' :=
  (tensorLeftIso M E X).inv ≫ tensorRightMap M f g ≫ (tensorLeftIso M E' Y).hom

/-- 左テンソルの射の基礎射は通常のテンソル射。 -/
lemma tensorLeftMap_hom {X Y : C} (g : X ⟶ Y) {E E' : Mod C M} (f : E ⟶ E') :
    (tensorLeftMap M g f).hom = g ⊗ₘ f.hom := by
  change (β_ E.X X).inv ≫ (f.hom ⊗ₘ g) ≫ (β_ E'.X Y).hom = _
  rw [BraidedCategory.braiding_naturality, Iso.inv_hom_id_assoc]

variable [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]

/-- 自由加群を左因子とする釣り合い積は、生成対象を加群の左へテンソルした加群と同型。 -/
def freeLeftIso (X : C) (E : Mod C M) :
    moduleObj M (MonoidalFreeModule.freeObj M X) E ≅ tensorLeftObj M X E :=
  swapIso M (MonoidalFreeModule.freeObj M X) E ≪≫ freeRightIso M E X ≪≫ tensorLeftIso M E X

/-- 左自由因子の比較は生成対象と加群の射の両方に関して自然。 -/
lemma freeLeft_naturality {X Y : C} (g : X ⟶ Y) {E E' : Mod C M} (f : E ⟶ E') :
    moduleMap M (MonoidalFreeModule.freeMap M g) f ≫ (freeLeftIso M Y E').hom =
      (freeLeftIso M X E).hom ≫ tensorLeftMap M g f := by
  simp only [freeLeftIso, Iso.trans_hom, tensorLeftMap, Category.assoc,
    Iso.hom_inv_id_assoc]
  slice_lhs 1 2 => rw [swap_naturality]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [freeRight_naturality]
  simp only [Category.assoc]

/-- 左自由因子の比較の逆射は生成元を第一因子へ挿入する。 -/
lemma freeLeftIso_inv (X : C) (E : Mod C M) :
    (freeLeftIso M X E).inv.hom = MonoidalFreeModule.generator M X ▷ E.X ≫
      projection M (MonoidalFreeModule.freeObj M X) E := by
  simp only [freeLeftIso, Iso.trans_inv, Mod.comp_hom', freeRightIso_inv, freeRightInv,
    Category.assoc]
  change (β_ E.X X).inv ≫ E.X ◁ MonoidalFreeModule.generator M X ≫
      projection M E (MonoidalFreeModule.freeObj M X) ≫
        swapHom M E (MonoidalFreeModule.freeObj M X) = _
  rw [projection_swapHom, BraidedCategory.braiding_naturality_right_assoc,
    Iso.inv_hom_id_assoc]

/-- 左自由因子の比較は生成元上で恒等射になる。 -/
@[reassoc] lemma generator_freeLeft_hom (X : C) (E : Mod C M) :
    MonoidalFreeModule.generator M X ▷ E.X ≫
        projection M (MonoidalFreeModule.freeObj M X) E ≫ (freeLeftIso M X E).hom.hom =
      𝟙 (X ⊗ E.X) := by
  rw [← Category.assoc, ← freeLeftIso_inv]
  exact congrArg Mod.Hom.hom (freeLeftIso M X E).inv_hom_id

/-- 自由加群を左因子とする釣り合いテンソル積の二変数関手。 -/
def freeLeftBifunctor : C × Mod C M ⥤ Mod C M :=
  (MonoidalFreeModule.freeFunctor M).prod (𝟭 (Mod C M)) ⋙ moduleBifunctor M

/-- 加群の左に対象をテンソルする二変数関手。 -/
def tensorLeftBifunctor : C × Mod C M ⥤ Mod C M where
  obj XE := tensorLeftObj M XE.1 XE.2
  map gf := tensorLeftMap M gf.1 gf.2
  map_id XE := by
    apply Mod.hom_ext
    rw [tensorLeftMap_hom, Mod.id_hom']
    exact id_tensorHom_id _ _
  map_comp gf hk := by
    apply Mod.hom_ext
    rw [Mod.comp_hom', tensorLeftMap_hom, tensorLeftMap_hom, tensorLeftMap_hom]
    change (gf.1 ≫ hk.1) ⊗ₘ (gf.2.hom ≫ hk.2.hom) = _
    exact (tensorHom_comp_tensorHom _ _ _ _).symm

/-- 左自由因子の比較を二変数の自然同型へまとめる。 -/
def freeLeftNatIso : freeLeftBifunctor M ≅ tensorLeftBifunctor M :=
  NatIso.ofComponents (fun XE => freeLeftIso M XE.1 XE.2)
    (fun gf => freeLeft_naturality M gf.1 gf.2)

end SerrePositivity.MonoidalBalancedTensor
end

end BalancedTensorFreeLeft

/-! ## BalancedTensorFreePair（旧 SerrePositivity/CategoryTheory/Monoidal/BalancedTensorFreePair.lean） -/

/-! # 二つの自由加群の釣り合いテンソル積 -/

@[expose] public section BalancedTensorFreePair
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
end

end BalancedTensorFreePair

/-! ## FreeModuleMonoidal（旧 SerrePositivity/CategoryTheory/Monoidal/FreeModuleMonoidal.lean） -/

/-! # 自由内部加群関手のモノイダル比較 -/

@[expose] public section FreeModuleMonoidal
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open MonoidalFreeModule

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (M : C) [MonObj M]

/-- 自由加群の生成元は入力の射と両立する。 -/
@[reassoc] lemma generator_freeMap {X Y : C} (f : X ⟶ Y) :
    generator M X ≫ (freeMap M f).hom = f ≫ generator M Y := by
  change ((λ_ X).inv ≫ η[M] ▷ X) ≫ M ◁ f = f ≫ (λ_ Y).inv ≫ η[M] ▷ Y
  rw [Category.assoc, ← whisker_exchange, ← leftUnitor_inv_naturality_assoc]

/-- 単位対象から生成した自由加群を正則加群へ比較する同型。 -/
def freeUnitIso : freeObj M (𝟙_ C) ≅ Mod.regular M := by
  let h := lift M (𝟙_ C) (Mod.regular M) η[M]
  have hh : h.hom = (ρ_ M).hom := MonObj.mul_one M
  letI : ModObj M (M ⊗ (𝟙_ C)) := freeAction M (𝟙_ C)
  letI : ModObj M M := (Mod.regular M).mod
  have : IsModHom M (ρ_ M).hom := by rw [← hh]; exact h.isModHom
  have : IsModHom M (ρ_ M).inv := inferInstance
  exact {
    hom := h
    inv := Mod.Hom.mk' (ρ_ M).inv IsModHom.smul_hom
    hom_inv_id := Mod.hom_ext _ _ (by
      change h.hom ≫ (ρ_ M).inv = 𝟙 _
      rw [hh, Iso.hom_inv_id])
    inv_hom_id := Mod.hom_ext _ _ (by
      change (ρ_ M).inv ≫ h.hom = 𝟙 _
      rw [hh, Iso.inv_hom_id]) }

/-- 自由加群の単位比較の順方向の基礎射は右単位同型。 -/
lemma freeUnitIso_hom : (freeUnitIso M).hom.hom = (ρ_ M).hom := MonObj.mul_one M

/-- 自由加群の単位比較の逆方向の基礎射は右単位同型の逆。 -/
lemma freeUnitIso_inv : (freeUnitIso M).inv.hom = (ρ_ M).inv := rfl

/-- 自由加群の単位比較は生成元を係数の単位へ送る。 -/
@[reassoc] lemma generator_freeUnit :
    generator M (𝟙_ C) ≫ (freeUnitIso M).hom.hom = η[M] :=
  generator_lift M (𝟙_ C) (Mod.regular M) η[M]

variable [SymmetricCategory C] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 三因子を左結合で自由加群の生成元へ分解する。 -/
@[reassoc] lemma generator_freeTriple_left (X Y Z : C) :
    generator M ((X ⊗ Y) ⊗ Z) ≫ (freePairIso M (X ⊗ Y) Z).inv.hom ≫
        (moduleMap M (freePairIso M X Y).inv (𝟙 (freeObj M Z))).hom =
      ((generator M X ⊗ₘ generator M Y) ⊗ₘ generator M Z) ≫
        tripleLeftProjection M (freeObj M X) (freeObj M Y) (freeObj M Z) := by
  rw [generator_freePair_inv_assoc]
  change (generator M (X ⊗ Y) ⊗ₘ generator M Z) ≫ projection M _ _ ≫
    map M (freePairIso M X Y).inv (𝟙 (freeObj M Z)) = _
  rw [projection_map, ← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Mod.id_hom', Category.comp_id, freeObj]
  rw [generator_freePair_inv]
  simp only [tripleLeftProjection]
  rw [← tensorHom_id, ← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]
  simp only [freeObj]

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 三因子を右結合で自由加群の生成元へ分解する。 -/
@[reassoc] lemma generator_freeTriple_right (X Y Z : C) :
    generator M (X ⊗ (Y ⊗ Z)) ≫ (freePairIso M X (Y ⊗ Z)).inv.hom ≫
        (moduleMap M (𝟙 (freeObj M X)) (freePairIso M Y Z).inv).hom =
      (generator M X ⊗ₘ (generator M Y ⊗ₘ generator M Z)) ≫
        tripleRightProjection M (freeObj M X) (freeObj M Y) (freeObj M Z) := by
  rw [generator_freePair_inv_assoc]
  change (generator M X ⊗ₘ generator M (Y ⊗ Z)) ≫ projection M _ _ ≫
    map M (𝟙 (freeObj M X)) (freePairIso M Y Z).inv = _
  rw [projection_map, ← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Mod.id_hom', Category.comp_id, freeObj]
  rw [generator_freePair_inv]
  simp only [tripleRightProjection]
  rw [← id_tensorHom, ← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]
  simp only [freeObj]

/-- 自由加群の積の逆比較は結合子と両立する。 -/
lemma freePair_associativity_inv (X Y Z : C) :
    (freePairIso M (X ⊗ Y) Z).inv ≫
        moduleMap M (freePairIso M X Y).inv (𝟙 (freeObj M Z)) ≫
          (associatorIso M (freeObj M X) (freeObj M Y) (freeObj M Z)).hom =
      freeMap M (α_ X Y Z).hom ≫ (freePairIso M X (Y ⊗ Z)).inv ≫
        moduleMap M (𝟙 (freeObj M X)) (freePairIso M Y Z).inv := by
  apply (freeHomEquiv M ((X ⊗ Y) ⊗ Z) _).injective
  change generator M ((X ⊗ Y) ⊗ Z) ≫ (freePairIso M (X ⊗ Y) Z).inv.hom ≫
      (moduleMap M (freePairIso M X Y).inv (𝟙 (freeObj M Z))).hom ≫
        associatorHom M (freeObj M X) (freeObj M Y) (freeObj M Z) =
    generator M ((X ⊗ Y) ⊗ Z) ≫ (freeMap M (α_ X Y Z).hom).hom ≫
      (freePairIso M X (Y ⊗ Z)).inv.hom ≫
        (moduleMap M (𝟙 (freeObj M X)) (freePairIso M Y Z).inv).hom
  rw [generator_freeTriple_left_assoc, tripleLeftProjection_associatorHom,
    generator_freeMap_assoc, generator_freeTriple_right]
  rw [MonoidalCategory.associator_naturality_assoc]

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 自由加群の積の逆比較は交換同型と両立する。 -/
lemma freePair_braiding_inv (X Y : C) :
    (freePairIso M X Y).inv ≫ (swapIso M (freeObj M X) (freeObj M Y)).hom =
      freeMap M (β_ X Y).hom ≫ (freePairIso M Y X).inv := by
  apply (freeHomEquiv M (X ⊗ Y) _).injective
  change generator M (X ⊗ Y) ≫ (freePairIso M X Y).inv.hom ≫
      swapHom M (freeObj M X) (freeObj M Y) =
    generator M (X ⊗ Y) ≫ (freeMap M (β_ X Y).hom).hom ≫ (freePairIso M Y X).inv.hom
  rw [generator_freePair_inv_assoc, projection_swapHom, generator_freeMap_assoc,
    generator_freePair_inv, BraidedCategory.braiding_naturality_assoc]

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 自由加群の単位と積の逆比較は左単位同型と両立する。 -/
lemma freePair_leftUnit_inv (X : C) :
    (leftUnitIso M (freeObj M X)).inv =
      freeMap M (λ_ X).inv ≫ (freePairIso M (𝟙_ C) X).inv ≫
        moduleMap M (freeUnitIso M).hom (𝟙 (freeObj M X)) := by
  apply (freeHomEquiv M X _).injective
  change generator M X ≫ leftUnitInv M (freeObj M X) =
    generator M X ≫ (freeMap M (λ_ X).inv).hom ≫ (freePairIso M (𝟙_ C) X).inv.hom ≫
      map M (freeUnitIso M).hom (𝟙 (freeObj M X))
  rw [generator_freeMap_assoc, generator_freePair_inv_assoc, projection_map]
  slice_rhs 2 3 => rw [tensorHom_comp_tensorHom]
  simp only [Mod.id_hom', Category.comp_id, freeObj]
  rw [generator_freeUnit]
  rw [leftUnitInv]
  change generator M X ≫ (λ_ (M ⊗ X)).inv ≫ η[M] ▷ (M ⊗ X) ≫
      projection M (Mod.regular M) (freeObj M X) =
    (λ_ X).inv ≫ (η[M] ⊗ₘ generator M X) ≫ projection M (Mod.regular M) (freeObj M X)
  erw [leftUnitor_inv_naturality_assoc]
  simp only [tensorHom_def', Category.assoc, freeObj]

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 自由加群の単位と積の逆比較は右単位同型と両立する。 -/
lemma freePair_rightUnit_inv (X : C) :
    (rightUnitIso M (freeObj M X)).inv =
      freeMap M (ρ_ X).inv ≫ (freePairIso M X (𝟙_ C)).inv ≫
        moduleMap M (𝟙 (freeObj M X)) (freeUnitIso M).hom := by
  apply (freeHomEquiv M X _).injective
  change generator M X ≫ rightUnitInv M (freeObj M X) =
    generator M X ≫ (freeMap M (ρ_ X).inv).hom ≫ (freePairIso M X (𝟙_ C)).inv.hom ≫
      map M (𝟙 (freeObj M X)) (freeUnitIso M).hom
  rw [generator_freeMap_assoc, generator_freePair_inv_assoc, projection_map]
  slice_rhs 2 3 => rw [tensorHom_comp_tensorHom]
  simp only [Mod.id_hom', Category.comp_id, freeObj]
  rw [generator_freeUnit]
  rw [rightUnitInv]
  change generator M X ≫ (ρ_ (M ⊗ X)).inv ≫ (M ⊗ X) ◁ η[M] ≫
      projection M (freeObj M X) (Mod.regular M) =
    (ρ_ X).inv ≫ (generator M X ⊗ₘ η[M]) ≫ projection M (freeObj M X) (Mod.regular M)
  erw [rightUnitor_inv_naturality_assoc]
  simp only [tensorHom_def, Category.assoc, freeObj]

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 自由加群の積の逆比較は両方の入力の射に関して自然。 -/
lemma freePair_inv_naturality {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (freePairIso M X Y).inv ≫ moduleMap M (freeMap M f) (freeMap M g) =
      freeMap M (f ⊗ₘ g) ≫ (freePairIso M X' Y').inv := by
  apply (cancel_epi (freePairIso M X Y).hom).1
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← freePair_naturality,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 自由加群関手の強モノイダル構造を比較同型と逆方向の整合性から構成する。 -/
def freeMonoidalCore : (freeFunctor M).CoreMonoidal :=
  Functor.CoreMonoidal.mk' (freeUnitIso M).symm (freePairIso M)
    (μIso_inv_natural_left := by
      intro X Y f Z
      have h := freePair_inv_naturality M f (𝟙 Z)
      have hi : freeMap M (𝟙 Z) = 𝟙 (freeObj M Z) := (freeFunctor M).map_id Z
      rw [hi, tensorHom_id] at h
      exact h)
    (μIso_inv_natural_right := by
      intro X Y Z f
      have h := freePair_inv_naturality M (𝟙 Z) f
      have hi : freeMap M (𝟙 Z) = 𝟙 (freeObj M Z) := (freeFunctor M).map_id Z
      rw [hi, id_tensorHom] at h
      exact h)
    (oplax_associativity := freePair_associativity_inv M)
    (oplax_left_unitality := freePair_leftUnit_inv M)
    (oplax_right_unitality := freePair_rightUnit_inv M)

/-- 自由内部加群関手は強モノイダル関手。 -/
instance freeFunctorMonoidal : (freeFunctor M).Monoidal := (freeMonoidalCore M).toMonoidal

/-- 自由内部加群関手は交換同型も保存する強モノイダル関手。 -/
instance freeFunctorBraided : (freeFunctor M).Braided where
  toMonoidal := freeFunctorMonoidal M
  braided := by
    intro X Y
    change (freePairIso M X Y).hom ≫ freeMap M (β_ X Y).hom =
      (swapIso M (freeObj M X) (freeObj M Y)).hom ≫ (freePairIso M Y X).hom
    apply (cancel_epi (freePairIso M X Y).inv).1
    rw [Iso.inv_hom_id_assoc, ← Category.assoc, freePair_braiding_inv,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.MonoidalBalancedTensor
end

end FreeModuleMonoidal

/-! ## BalancedTensorFreeUnit（旧 SerrePositivity/CategoryTheory/Monoidal/BalancedTensorFreeUnit.lean） -/

/-! # 単位と同型な対象からの自由加群の左テンソルの比較 -/

@[expose] public section BalancedTensorFreeUnit
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (M : C) [MonObj M]

/-- 単位と同型な対象から生成した自由加群を正則加群へ比較する。 -/
def freeUnitFromIso {S : C} (e : S ≅ 𝟙_ C) :
    MonoidalFreeModule.freeObj M S ≅ Mod.regular M :=
  (MonoidalFreeModule.freeFunctor M).mapIso e ≪≫ freeUnitIso M

/-- この比較は生成元を単位への比較と係数の単位の合成へ送る。 -/
@[reassoc]
lemma generator_freeUnitFromIso {S : C} (e : S ≅ 𝟙_ C) :
    MonoidalFreeModule.generator M S ≫ (freeUnitFromIso M e).hom.hom = e.hom ≫ η[M] := by
  unfold freeUnitFromIso
  simp only [Iso.trans_hom, Mod.comp_hom']
  change MonoidalFreeModule.generator M S ≫ (MonoidalFreeModule.freeMap M e.hom).hom ≫
    (freeUnitIso M).hom.hom = _
  rw [generator_freeMap_assoc, generator_freeUnit]

variable [SymmetricCategory C] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

/-- 左自由因子の逆比較と単位比較を合成すると通常の左単位子になる。 -/
lemma freeLeft_unit_comparison {S : C} (e : S ≅ 𝟙_ C) (A : Mod C M) :
    (freeLeftIso M S A).inv.hom ≫
        (((freeUnitFromIso M e).hom ▷ A) ≫ (λ_ A).hom).hom =
      e.hom ▷ A.X ≫ (λ_ A.X).hom := by
  rw [freeLeftIso_inv]
  change (MonoidalFreeModule.generator M S ▷ A.X ≫
    projection M (MonoidalFreeModule.freeObj M S) A) ≫
      map M (freeUnitFromIso M e).hom (𝟙 A) ≫ leftUnitHom M A = _
  rw [Category.assoc, projection_map_assoc, Mod.id_hom', tensorHom_id,
    projection_leftUnitHom]
  rw [← comp_whiskerRight_assoc, generator_freeUnitFromIso, comp_whiskerRight,
    Category.assoc, ModObj.one_smul_self]

end SerrePositivity.MonoidalBalancedTensor
end

end BalancedTensorFreeUnit

/-! ## BalancedTensorFreeAssociator（旧 SerrePositivity/CategoryTheory/Monoidal/BalancedTensorFreeAssociator.lean） -/

/-! # 二つの左自由因子の結同比較と基礎圏の結合子 -/

@[expose] public section BalancedTensorFreeAssociator
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
end

end BalancedTensorFreeAssociator

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.8.4.11" (partial := component) "仮定：通常のモノイダル圏の内部モノイド A（Lean が強い：左加群と右外部作用の版。モノイダル opposite により左右を交換できる）。結論：自由忘却随伴を構成し、自由対象 (A⊗X) の Y による右テンソルを A⊗(X⊗Y) と自然に同定する（この仮定での HA の結論の一部に一致）。一般の ∞ 圏の相対随伴と coherent な線型関手の比較は含まれない。"] _root_.SerrePositivity.MonoidalBalancedTensor.freeTensorIso
attribute [cite HA "4.8.4.11" (partial := component) "仮定：通常のモノイダル圏の内部モノイド A（Lean が強い：左加群と右外部作用の版。モノイダル opposite により左右を交換できる）。結論：自由忘却随伴を構成し、自由対象 (A⊗X) の Y による右テンソルを A⊗(X⊗Y) と自然に同定する（この仮定での HA の結論の一部に一致）。一般の ∞ 圏の相対随伴と coherent な線型関手の比較は含まれない。"] _root_.SerrePositivity.MonoidalBalancedTensor.freeTensor_naturality
