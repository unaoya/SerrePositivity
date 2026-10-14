module

public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorRightUnit
public import SerrePositivity.CategoryTheory.Monoidal.FreeModule

/-! # 自由加群を右因子とする釣り合いテンソル積 -/

@[expose] public section

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
