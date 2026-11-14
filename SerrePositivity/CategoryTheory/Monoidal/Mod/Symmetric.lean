module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.CategoryTheory.Monoidal.Mod.Monoidal
public import Mathlib.Tactic.CategoryTheory.Slice

/-!
# Monoidal.Mod.Symmetric

## 概要
関連する圏論の構成と補題をまとめる。各構成の詳細は以下の元モジュールの説明を参照。

## 方針
元の宣言と証明を保持し、依存順に section を分けて配置する。

## 規約
公開宣言名・名前空間・宇宙変数の意味を変更しない。元の module docstring は各節に保存する。

## 使われ方
旧モジュールの利用元は `SerrePositivity.CategoryTheory.Monoidal.Mod.Symmetric` を直接 import する。
-/

/-! ## BalancedTensorSymmetry（旧 SerrePositivity/CategoryTheory/Monoidal/BalancedTensorSymmetry.lean） -/

/-! # 釣り合いテンソル積の交換同型 -/

@[expose] public section BalancedTensorSymmetry
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
end

end BalancedTensorSymmetry

/-! ## BalancedTensorHexagon（旧 SerrePositivity/CategoryTheory/Monoidal/BalancedTensorHexagon.lean） -/

/-! # 釣り合いテンソル積のhexagon整合性 -/

@[expose] public section BalancedTensorHexagon
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  (M : C) [MonObj M] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]

/-- 右結合の三因子の標準射の外側の交換を計算する。 -/
@[reassoc] lemma tripleRightProjection_swap (E F G : Mod C M) :
    tripleRightProjection M E F G ≫ swapHom M E (moduleObj M F G) =
      (β_ E.X (F.X ⊗ G.X)).hom ≫ tripleLeftProjection M F G E := by
  rw [tripleRightProjection, Category.assoc, projection_swapHom]
  erw [BraidedCategory.braiding_naturality_right_assoc]
  rfl

/-- 左結合の三因子の標準射の外側の交換を計算する。 -/
@[reassoc] lemma tripleLeftProjection_swap (E F G : Mod C M) :
    tripleLeftProjection M E F G ≫ swapHom M (moduleObj M E F) G =
      (β_ (E.X ⊗ F.X) G.X).hom ≫ tripleRightProjection M G E F := by
  rw [tripleLeftProjection, Category.assoc, projection_swapHom]
  erw [BraidedCategory.braiding_naturality_left_assoc]
  rfl

/-- 左結合の三因子の標準射の内側の交換を計算する。 -/
@[reassoc] lemma tripleLeftProjection_map_swap (E F G : Mod C M) :
    tripleLeftProjection M E F G ≫ map M (swapIso M E F).hom (𝟙 G) =
      (β_ E.X F.X).hom ▷ G.X ≫ tripleLeftProjection M F E G := by
  rw [tripleLeftProjection, Category.assoc, projection_map]
  change projection M E F ▷ G.X ≫ (swapHom M E F ⊗ₘ 𝟙 G.X) ≫
    projection M (moduleObj M F E) G = _
  rw [tensorHom_id, ← comp_whiskerRight_assoc, projection_swapHom, comp_whiskerRight]
  simp only [tripleLeftProjection, Category.assoc]

/-- 右結合の三因子の標準射の内側の交換を計算する。 -/
@[reassoc] lemma tripleRightProjection_map_swap (E F G : Mod C M) :
    tripleRightProjection M E F G ≫ map M (𝟙 E) (swapIso M F G).hom =
      E.X ◁ (β_ F.X G.X).hom ≫ tripleRightProjection M E G F := by
  rw [tripleRightProjection, Category.assoc, projection_map]
  change E.X ◁ projection M F G ≫ (𝟙 E.X ⊗ₘ swapHom M F G) ≫
    projection M E (moduleObj M G F) = _
  rw [id_tensorHom, ← whiskerLeft_comp_assoc, projection_swapHom, whiskerLeft_comp]
  simp only [tripleRightProjection, Category.assoc]

variable [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

/-- 釣り合いテンソル積の結合・交換同型は順方向のhexagonを満たす。 -/
lemma hexagon_forward (E F G : Mod C M) :
    (associatorIso M E F G).hom ≫ (swapIso M E (moduleObj M F G)).hom ≫
        (associatorIso M F G E).hom =
      moduleMap M (swapIso M E F).hom (𝟙 G) ≫ (associatorIso M F E G).hom ≫
        moduleMap M (𝟙 F) (swapIso M E G).hom := by
  apply Mod.hom_ext
  apply (cancel_epi (tripleLeftProjection M E F G)).1
  change tripleLeftProjection M E F G ≫ associatorHom M E F G ≫
      swapHom M E (moduleObj M F G) ≫ associatorHom M F G E =
    tripleLeftProjection M E F G ≫ map M (swapIso M E F).hom (𝟙 G) ≫
      associatorHom M F E G ≫ map M (𝟙 F) (swapIso M E G).hom
  rw [tripleLeftProjection_associatorHom_assoc, tripleRightProjection_swap_assoc,
    tripleLeftProjection_associatorHom, tripleLeftProjection_map_swap_assoc,
    tripleLeftProjection_associatorHom_assoc, tripleRightProjection_map_swap,
    BraidedCategory.hexagon_forward_assoc]

/-- 釣り合いテンソル積の結合・交換同型は逆方向のhexagonを満たす。 -/
lemma hexagon_reverse (E F G : Mod C M) :
    (associatorIso M E F G).inv ≫ (swapIso M (moduleObj M E F) G).hom ≫
        (associatorIso M G E F).inv =
      moduleMap M (𝟙 E) (swapIso M F G).hom ≫ (associatorIso M E G F).inv ≫
        moduleMap M (swapIso M E G).hom (𝟙 F) := by
  apply Mod.hom_ext
  apply (cancel_epi (tripleRightProjection M E F G)).1
  change tripleRightProjection M E F G ≫ associatorInv M E F G ≫
      swapHom M (moduleObj M E F) G ≫ associatorInv M G E F =
    tripleRightProjection M E F G ≫ map M (𝟙 E) (swapIso M F G).hom ≫
      associatorInv M E G F ≫ map M (swapIso M E G).hom (𝟙 F)
  rw [tripleRightProjection_associatorInv_assoc, tripleLeftProjection_swap_assoc,
    tripleRightProjection_associatorInv, tripleRightProjection_map_swap_assoc,
    tripleRightProjection_associatorInv_assoc, tripleLeftProjection_map_swap,
    BraidedCategory.hexagon_reverse_assoc]

end SerrePositivity.MonoidalBalancedTensor
end

end BalancedTensorHexagon

/-! ## BalancedTensorSymmetric（旧 SerrePositivity/CategoryTheory/Monoidal/BalancedTensorSymmetric.lean） -/

/-! # 可換モノイド上の内部加群の対称モノイダル構造 -/

@[expose] public section BalancedTensorSymmetric
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  (M : C) [MonObj M] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

/-- 釣り合いテンソル積と商上の交換による内部加群圏の対称モノイダル構造。 -/
instance symmetricCategory : SymmetricCategory (Mod C M) where
  braiding := swapIso M
  braiding_naturality_right := by
    intro E F G f
    exact swap_naturality M (𝟙 E) f
  braiding_naturality_left := by
    intro E F f G
    exact swap_naturality M f (𝟙 G)
  hexagon_forward := hexagon_forward M
  hexagon_reverse := hexagon_reverse M
  symmetry := swapIso_symmetry M

/-- 登録した内部加群のbraidingは構成済みの釣り合い商の交換同型。 -/
lemma braiding_eq_swapIso (E F : Mod C M) : β_ E F = swapIso M E F := rfl

end SerrePositivity.MonoidalBalancedTensor
end

end BalancedTensorSymmetric

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.4.3.13" (partial := special) "仮定：通常の対称閉モノイダル圏の可換内部モノイドと、内部 Hom と平衡テンソルを作る等化子・余等化子および保存条件（Lean が強い：通常の対称閉モノイダル圏と指定した等化子・余等化子）。結論：平衡テンソルは内部 Hom の左随伴なので通常圏の余極限を保存し、組紐によってもう一方の変数でも保存する（この仮定での HA の結論の一部に一致）。一般の幾何学的実現は含まれない。"] _root_.SerrePositivity.MonoidalBalancedTensor.symmetricCategory
attribute [cite HA "4.5.2.1" (partial := special) "仮定：通常の対称モノイダル圏の可換内部モノイド A と必要な余等化子およびテンソルによる保存条件（Lean が強い：通常圏に限る）。結論：内部左加群に組紐から右作用を入れ、その作用で平衡化した相対テンソルを積とする対称モノイダル構造を構成する（この仮定での HA の結論の一部に一致）。(1) の通常圏の場合と (2) のテンソル公式に対応し、∞ オペラッド間のモノイダル比較は含まれない。"] _root_.SerrePositivity.MonoidalBalancedTensor.symmetricCategory
