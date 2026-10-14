module

public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorLeftUnit
public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorRightUnit
public import Mathlib.Tactic.CategoryTheory.Slice

/-! # 釣り合いテンソル積の交換同型 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  (M : C) [MonObj M]

/-- 釣り合い関係式の三因子を逆順へ移す射。 -/
def swapRelation (E F : Mod C M) : (E.X ⊗ M) ⊗ F.X ⟶ (F.X ⊗ M) ⊗ E.X :=
  (α_ E.X M F.X).hom ≫ (β_ E.X (M ⊗ F.X)).hom ≫ (β_ M F.X).hom ▷ E.X

/-- 関係式の三因子の交換を、反対側の結合順で書く。 -/
lemma swapRelation_eq (E F : Mod C M) :
    swapRelation M E F = (β_ (E.X ⊗ M) F.X).hom ≫
      F.X ◁ (β_ E.X M).hom ≫ (α_ F.X M E.X).inv := by
  rw [swapRelation, ← BraidedCategory.braiding_naturality_right,
    BraidedCategory.braiding_tensor_right_hom]
  rw [BraidedCategory.braiding_tensor_left_hom]
  simp only [Category.assoc]

/-- 交換射は第一因子の作用による関係式を第二因子の作用へ移す。 -/
@[reassoc] lemma swap_relationLeft (E F : Mod C M) :
    relationLeft M E F ≫ (β_ E.X F.X).hom =
      swapRelation M E F ≫ relationRight M F E := by
  rw [relationLeft, BraidedCategory.braiding_naturality_left, swapRelation_eq, relationRight]
  simp only [rightActionMap, whiskerLeft_comp, Category.assoc, Iso.inv_hom_id_assoc]

/-- 交換射は第二因子の作用による関係式を第一因子の作用へ移す。 -/
@[reassoc] lemma swap_relationRight (E F : Mod C M) :
    relationRight M E F ≫ (β_ E.X F.X).hom =
      swapRelation M E F ≫ relationLeft M F E := by
  rw [relationRight, Category.assoc, BraidedCategory.braiding_naturality_right,
    swapRelation, relationLeft]
  simp only [rightActionMap, comp_whiskerRight, Category.assoc]
  slice_rhs 3 4 => rw [← comp_whiskerRight, SymmetricCategory.symmetry]
  simp only [id_whiskerRight, Category.id_comp]


variable [HasCoequalizers C]

/-- 基礎圏の交換射と標準射の合成は釣り合い条件を満たす。 -/
def swapBalanced (E F : Mod C M) : BalancedMap M E F (obj M F E) :=
  ⟨(β_ E.X F.X).hom ≫ projection M F E, by
    rw [← Category.assoc, swap_relationLeft, Category.assoc, ← projection_condition,
      ← Category.assoc, ← swap_relationRight, Category.assoc]⟩

/-- 基礎圏の交換射を釣り合い商へ降ろした射。 -/
def swapHom (E F : Mod C M) : obj M E F ⟶ obj M F E := desc M (swapBalanced M E F)

/-- 商上の交換射は標準射上で基礎圏の交換射に一致する。 -/
@[reassoc (attr := simp)] lemma projection_swapHom (E F : Mod C M) :
    projection M E F ≫ swapHom M E F = (β_ E.X F.X).hom ≫ projection M F E :=
  projection_desc M _

/-- 商上で二回交換すると恒等射になる。 -/
lemma swapHom_swapHom (E F : Mod C M) : swapHom M E F ≫ swapHom M F E = 𝟙 _ := by
  apply hom_ext M
  rw [projection_swapHom_assoc, projection_swapHom, SymmetricCategory.symmetry_assoc,
    Category.comp_id]

/-- 釣り合いテンソル積の基礎対象の交換同型。 -/
def swapUnderlyingIso (E F : Mod C M) : obj M E F ≅ obj M F E where
  hom := swapHom M E F
  inv := swapHom M F E
  hom_inv_id := swapHom_swapHom M E F
  inv_hom_id := swapHom_swapHom M F E

variable [IsCommMonObj M]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]

/-- 商上の交換射は加群作用と両立する。 -/
def swapModuleHom (E F : Mod C M) : moduleObj M E F ⟶ moduleObj M F E :=
  moduleDesc M (swapBalanced M E F) (by
    change (α_ M E.X F.X).inv ≫ γ[M,E.X] ▷ F.X ≫
        (β_ E.X F.X).hom ≫ projection M F E =
      M ◁ ((β_ E.X F.X).hom ≫ projection M F E) ≫ γ[M,(moduleObj M F E).X]
    rw [whiskerLeft_comp, Category.assoc, projection_action,
      BraidedCategory.braiding_naturality_left_assoc]
    have hc : F.X ◁ γ[M,E.X] ≫ projection M F E =
        (α_ F.X M E.X).inv ≫ rightActionMap M F ▷ E.X ≫ projection M F E := by
      have h := projection_condition M F E
      change rightActionMap M F ▷ E.X ≫ projection M F E =
        ((α_ F.X M E.X).hom ≫ F.X ◁ γ[M,E.X]) ≫ projection M F E at h
      rw [h, Category.assoc, Iso.inv_hom_id_assoc]
    rw [hc]
    erw [BraidedCategory.braiding_tensor_left_hom]
    simp only [rightActionMap, comp_whiskerRight, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
    slice_lhs 3 4 => rw [← comp_whiskerRight, SymmetricCategory.symmetry]
    simp only [id_whiskerRight, Category.id_comp])

/-- 釣り合いテンソル積の加群としての交換同型。 -/
def swapIso (E F : Mod C M) : moduleObj M E F ≅ moduleObj M F E where
  hom := swapModuleHom M E F
  inv := swapModuleHom M F E
  hom_inv_id := Mod.hom_ext _ _ (swapHom_swapHom M E F)
  inv_hom_id := Mod.hom_ext _ _ (swapHom_swapHom M F E)

/-- 交換同型は両方の加群の射に関して自然。 -/
lemma swap_naturality {E E' F F' : Mod C M} (f : E ⟶ E') (g : F ⟶ F') :
    moduleMap M f g ≫ (swapIso M E' F').hom = (swapIso M E F).hom ≫ moduleMap M g f := by
  apply Mod.hom_ext
  apply hom_ext M
  change projection M E F ≫ map M f g ≫ swapHom M E' F' =
    projection M E F ≫ swapHom M E F ≫ map M g f
  rw [projection_map_assoc, projection_swapHom, projection_swapHom_assoc, projection_map]
  rw [BraidedCategory.braiding_naturality_assoc]

/-- 加群として二回交換すると恒等射になる。 -/
lemma swapIso_symmetry (E F : Mod C M) : (swapIso M E F).hom ≫ (swapIso M F E).hom = 𝟙 _ :=
  (swapIso M E F).hom_inv_id

/-- 二変数関手の入力を入れ替える交換自然同型。 -/
def swapNatIso : moduleBifunctor M ≅
    CategoryTheory.Prod.swap (CategoryTheory.Mod C M) (CategoryTheory.Mod C M) ⋙
      moduleBifunctor M :=
  NatIso.ofComponents (fun EF => swapIso M EF.1 EF.2)
    (fun fg => swap_naturality M fg.1 fg.2)

/-- 正則加群との交換を左単位比較へ続けると右単位比較になる。 -/
lemma swapIso_rightUnit (E : Mod C M) :
    swapIso M E (Mod.regular M) ≪≫ leftUnitIso M E = rightUnitIso M E := by
  apply Iso.ext
  apply Mod.hom_ext
  apply hom_ext M
  change projection M E (Mod.regular M) ≫ swapHom M E (Mod.regular M) ≫
      leftUnitHom M E = projection M E (Mod.regular M) ≫ rightUnitHom M E
  rw [projection_swapHom_assoc, projection_leftUnitHom, projection_rightUnitHom]
  rfl

end SerrePositivity.MonoidalBalancedTensor
