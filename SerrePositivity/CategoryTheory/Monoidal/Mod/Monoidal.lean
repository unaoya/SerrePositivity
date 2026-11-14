module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.CategoryTheory.Monoidal.Mod.BalancedTensor
public import Mathlib.Tactic.CategoryTheory.Slice

/-!
# Monoidal.Mod.Monoidal

## 概要
関連する圏論の構成と補題をまとめる。各構成の詳細は以下の元モジュールの説明を参照。

## 方針
元の宣言と証明を保持し、依存順に section を分けて配置する。

## 規約
公開宣言名・名前空間・宇宙変数の意味を変更しない。元の module docstring は各節に保存する。

## 使われ方
旧モジュールの利用元は `SerrePositivity.CategoryTheory.Monoidal.Mod.Monoidal` を直接 import する。
-/

/-! ## BalancedTensorAssociator（旧 SerrePositivity/CategoryTheory/Monoidal/BalancedTensorAssociator.lean） -/

/-! # 釣り合いテンソル積の結合比較 -/

@[expose] public section BalancedTensorAssociator
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (M : C) [MonObj M] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 右結合の標準射は、左側の二因子の釣り合い関係式と両立する。 -/
lemma associatorSeed_balanced (E F G : Mod C M) :
    relationLeft M E F ▷ G.X ≫ (α_ E.X F.X G.X).hom ≫ tripleRightProjection M E F G =
      relationRight M E F ▷ G.X ≫ (α_ E.X F.X G.X).hom ≫
        tripleRightProjection M E F G := by
  simp only [relationLeft, relationRight, tripleRightProjection, comp_whiskerRight,
    Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc]
  have h := projection_condition M E (moduleObj M F G)
  change rightActionMap M E ▷ (obj M F G) ≫ projection M E (moduleObj M F G) =
    ((α_ E.X M (obj M F G)).hom ≫ E.X ◁ γ[M,(moduleObj M F G).X]) ≫
      projection M E (moduleObj M F G) at h
  erw [h]
  simp only [Category.assoc]
  rw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc, projection_action,
    whiskerLeft_comp, whiskerLeft_comp]
  rw [associator_naturality_middle_assoc]
  have hc : (α_ (E.X ⊗ M) F.X G.X).hom ≫ (α_ E.X M (F.X ⊗ G.X)).hom ≫
      E.X ◁ (α_ M F.X G.X).inv =
    (α_ E.X M F.X).hom ▷ G.X ≫ (α_ E.X (M ⊗ F.X) G.X).hom := by monoidal
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ E.X ◁ (γ[M,F.X] ▷ G.X) ≫ E.X ◁ projection M F G ≫
      projection M E (moduleObj M F G)) hc

/-- 左側の二因子の商へ降ろした結合比較の第一段階。 -/
def associatorStep (E F G : Mod C M) : obj M E F ⊗ G.X ⟶ obj M E (moduleObj M F G) :=
  descRight M E F G.X ((α_ E.X F.X G.X).hom ≫ tripleRightProjection M E F G)
    (by simpa only [Category.assoc] using associatorSeed_balanced M E F G)

/-- 第一段階の結合比較は標準射上で基礎圏の結合子に一致する。 -/
@[reassoc] lemma projection_associatorStep (E F G : Mod C M) :
    projection M E F ▷ G.X ≫ associatorStep M E F G =
      (α_ E.X F.X G.X).hom ≫ tripleRightProjection M E F G := projection_descRight M _ _ _ _ _

/-- 第一段階の比較は残る二因子の釣り合い条件も満たす。 -/
lemma associatorStep_balanced (E F G : Mod C M) :
    relationLeft M (moduleObj M E F) G ≫ associatorStep M E F G =
      relationRight M (moduleObj M E F) G ≫ associatorStep M E F G := by
  have : Epi ((projection M E F ▷ M) ▷ G.X) := inferInstanceAs
    (Epi (((tensorRight M) ⋙ tensorRight G.X).map
      (coequalizer.π (relationLeft M E F) (relationRight M E F))))
  apply (cancel_epi ((projection M E F ▷ M) ▷ G.X)).1
  simp only [relationLeft, relationRight, Category.assoc]
  change (projection M E F ▷ M) ▷ G.X ≫
      rightActionMap M (moduleObj M E F) ▷ G.X ≫ associatorStep M E F G =
    (projection M E F ▷ M) ▷ G.X ≫ (α_ (obj M E F) M G.X).hom ≫
      (obj M E F) ◁ γ[M,G.X] ≫ associatorStep M E F G
  rw [← comp_whiskerRight_assoc, projection_rightAction, comp_whiskerRight,
    comp_whiskerRight, Category.assoc, Category.assoc, projection_associatorStep,
    associator_naturality_middle_assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, projection_associatorStep,
    associator_naturality_right_assoc]
  simp only [tripleRightProjection]
  rw [← whiskerLeft_comp_assoc]
  have h := projection_condition M F G
  change rightActionMap M F ▷ G.X ≫ projection M F G =
    ((α_ F.X M G.X).hom ≫ F.X ◁ γ[M,G.X]) ≫ projection M F G at h
  rw [h, whiskerLeft_comp, whiskerLeft_comp]
  have hc : (α_ E.X F.X M).hom ▷ G.X ≫ (α_ E.X (F.X ⊗ M) G.X).hom ≫
      E.X ◁ (α_ F.X M G.X).hom =
    (α_ (E.X ⊗ F.X) M G.X).hom ≫ (α_ E.X F.X (M ⊗ G.X)).hom := by monoidal
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ E.X ◁ F.X ◁ γ[M,G.X] ≫ E.X ◁ projection M F G ≫
      projection M E (moduleObj M F G)) hc

/-- 二段の釣り合い商へ降ろした結合比較の順方向。 -/
def associatorHom (E F G : Mod C M) :
    obj M (moduleObj M E F) G ⟶ obj M E (moduleObj M F G) :=
  desc M ⟨associatorStep M E F G, associatorStep_balanced M E F G⟩

/-- 結合比較の順方向は三つの因子からの標準射上で結合子に一致する。 -/
@[reassoc] lemma tripleLeftProjection_associatorHom (E F G : Mod C M) :
    tripleLeftProjection M E F G ≫ associatorHom M E F G =
      (α_ E.X F.X G.X).hom ≫ tripleRightProjection M E F G := by
  rw [tripleLeftProjection, Category.assoc, associatorHom, projection_desc,
    projection_associatorStep]

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 左結合の標準射は右側の二因子の釣り合い関係式と両立する。 -/
lemma associatorInvSeed_balanced (E F G : Mod C M) :
    E.X ◁ relationLeft M F G ≫ (α_ E.X F.X G.X).inv ≫ tripleLeftProjection M E F G =
      E.X ◁ relationRight M F G ≫ (α_ E.X F.X G.X).inv ≫
        tripleLeftProjection M E F G := by
  simp only [relationLeft, relationRight, tripleLeftProjection, whiskerLeft_comp,
    Category.assoc]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc]
  have h : E.X ◁ rightActionMap M F ≫ projection M E F =
      (α_ E.X F.X M).inv ≫ projection M E F ▷ M ≫
        rightActionMap M (moduleObj M E F) := by
    rw [projection_rightAction, Iso.inv_hom_id_assoc]
  rw [h, comp_whiskerRight, comp_whiskerRight]
  simp only [Category.assoc]
  have hc := projection_condition M (moduleObj M E F) G
  change rightActionMap M (moduleObj M E F) ▷ G.X ≫ projection M (moduleObj M E F) G =
    ((α_ (obj M E F) M G.X).hom ≫ (obj M E F) ◁ γ[M,G.X]) ≫
      projection M (moduleObj M E F) G at hc
  erw [hc]
  simp only [Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc]
  rw [associator_inv_naturality_right_assoc]
  have hk : (α_ E.X (F.X ⊗ M) G.X).inv ≫ (α_ E.X F.X M).inv ▷ G.X ≫
      (α_ (E.X ⊗ F.X) M G.X).hom =
    E.X ◁ (α_ F.X M G.X).hom ≫ (α_ E.X F.X (M ⊗ G.X)).inv := by monoidal
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ (E.X ⊗ F.X) ◁ γ[M,G.X] ≫ projection M E F ▷ G.X ≫
      projection M (moduleObj M E F) G) hk

/-- 右側の二因子の商へ降ろした逆結合比較の第一段階。 -/
def associatorInvStep (E F G : Mod C M) : E.X ⊗ obj M F G ⟶ obj M (moduleObj M E F) G :=
  descLeft M E.X F G ((α_ E.X F.X G.X).inv ≫ tripleLeftProjection M E F G)
    (by simpa only [Category.assoc] using associatorInvSeed_balanced M E F G)

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 逆比較の第一段階は標準射上で結合子の逆に一致する。 -/
@[reassoc] lemma projection_associatorInvStep (E F G : Mod C M) :
    E.X ◁ projection M F G ≫ associatorInvStep M E F G =
      (α_ E.X F.X G.X).inv ≫ tripleLeftProjection M E F G :=
  projection_descLeft M _ _ _ _ _

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 逆比較の第一段階は残る二因子の釣り合い条件も満たす。 -/
lemma associatorInvStep_balanced (E F G : Mod C M) :
    relationLeft M E (moduleObj M F G) ≫ associatorInvStep M E F G =
      relationRight M E (moduleObj M F G) ≫ associatorInvStep M E F G := by
  have : Epi ((E.X ⊗ M) ◁ projection M F G) := inferInstance
  apply (cancel_epi ((E.X ⊗ M) ◁ projection M F G)).1
  simp only [relationLeft, relationRight, Category.assoc]
  change (E.X ⊗ M) ◁ projection M F G ≫ rightActionMap M E ▷ (obj M F G) ≫
      associatorInvStep M E F G =
    (E.X ⊗ M) ◁ projection M F G ≫ (α_ E.X M (obj M F G)).hom ≫
      E.X ◁ γ[M,(moduleObj M F G).X] ≫ associatorInvStep M E F G
  rw [whisker_exchange_assoc, projection_associatorInvStep,
    associator_inv_naturality_left_assoc, associator_naturality_right_assoc,
    ← whiskerLeft_comp_assoc, projection_action, whiskerLeft_comp, whiskerLeft_comp]
  rw [Category.assoc, Category.assoc, projection_associatorInvStep]
  erw [associator_inv_naturality_middle_assoc]
  simp only [tripleLeftProjection]
  rw [← comp_whiskerRight_assoc]
  have h := projection_condition M E F
  change rightActionMap M E ▷ F.X ≫ projection M E F =
    ((α_ E.X M F.X).hom ≫ E.X ◁ γ[M,F.X]) ≫ projection M E F at h
  rw [h, comp_whiskerRight, comp_whiskerRight]
  have hk : (α_ (E.X ⊗ M) F.X G.X).inv ≫ (α_ E.X M F.X).hom ▷ G.X =
    (α_ E.X M (F.X ⊗ G.X)).hom ≫ E.X ◁ (α_ M F.X G.X).inv ≫
      (α_ E.X (M ⊗ F.X) G.X).inv := by monoidal
  simpa only [Category.assoc, MonoidalLeftActionStruct.actionObj] using congrArg
    (fun k => k ≫ (E.X ◁ γ[M,F.X]) ▷ G.X ≫ projection M E F ▷ G.X ≫
      projection M (moduleObj M E F) G) hk

/-- 二段の釣り合い商へ降ろした結合比較の逆方向。 -/
def associatorInv (E F G : Mod C M) :
    obj M E (moduleObj M F G) ⟶ obj M (moduleObj M E F) G :=
  desc M ⟨associatorInvStep M E F G, associatorInvStep_balanced M E F G⟩

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 結合比較の逆方向は三つの因子からの標準射上で結合子の逆に一致する。 -/
@[reassoc] lemma tripleRightProjection_associatorInv (E F G : Mod C M) :
    tripleRightProjection M E F G ≫ associatorInv M E F G =
      (α_ E.X F.X G.X).inv ≫ tripleLeftProjection M E F G := by
  rw [tripleRightProjection, Category.assoc, associatorInv, projection_desc,
    projection_associatorInvStep]

/-- 反復釣り合いテンソル積の基礎対象の結合同型。 -/
def associatorUnderlyingIso (E F G : Mod C M) :
    obj M (moduleObj M E F) G ≅ obj M E (moduleObj M F G) where
  hom := associatorHom M E F G
  inv := associatorInv M E F G
  hom_inv_id := by
    apply (cancel_epi (tripleLeftProjection M E F G)).1
    rw [tripleLeftProjection_associatorHom_assoc, tripleRightProjection_associatorInv,
      Iso.hom_inv_id_assoc, Category.comp_id]
  inv_hom_id := by
    apply (cancel_epi (tripleRightProjection M E F G)).1
    rw [tripleRightProjection_associatorInv_assoc, tripleLeftProjection_associatorHom,
      Iso.inv_hom_id_assoc, Category.comp_id]

/-- 左結合の三因子の標準射を、加群の射として構成する。 -/
def tripleLeftModuleHom (E F G : Mod C M) :
    tensorRightObj M (tensorRightObj M E F.X) G.X ⟶ moduleObj M (moduleObj M E F) G :=
  tensorRightMap M (projectionModuleHom M E F) (𝟙 G.X) ≫
    projectionModuleHom M (moduleObj M E F) G

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 左結合の三因子の標準射の加群としての基礎射。 -/
lemma tripleLeftModuleHom_hom (E F G : Mod C M) :
    (tripleLeftModuleHom M E F G).hom = tripleLeftProjection M E F G := by
  change (projection M E F ⊗ₘ 𝟙 G.X) ≫ projection M (moduleObj M E F) G = _
  rw [tensorHom_id]
  rfl

/-- 右結合の三因子の標準射を、加群の射として構成する。 -/
def tripleRightModuleHom (E F G : Mod C M) :
    tensorRightObj M E (F.X ⊗ G.X) ⟶ moduleObj M E (moduleObj M F G) :=
  tensorRightMap M (𝟙 E) (projection M F G) ≫ projectionModuleHom M E (moduleObj M F G)

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 右結合の三因子の標準射の加群としての基礎射。 -/
lemma tripleRightModuleHom_hom (E F G : Mod C M) :
    (tripleRightModuleHom M E F G).hom = tripleRightProjection M E F G := by
  change (𝟙 E.X ⊗ₘ projection M F G) ≫ projection M E (moduleObj M F G) = _
  rw [id_tensorHom]
  rfl

/-- 結合比較の順方向は加群作用と両立する。 -/
def associatorModuleHom (E F G : Mod C M) :
    moduleObj M (moduleObj M E F) G ⟶ moduleObj M E (moduleObj M F G) :=
  Mod.Hom.mk' (associatorHom M E F G) (by
    have : Epi (M ◁ (projection M E F ▷ G.X)) := inferInstanceAs
      (Epi (((tensorRight G.X) ⋙ tensorLeft M).map
        (coequalizer.π (relationLeft M E F) (relationRight M E F))))
    have : Epi (M ◁ tripleLeftProjection M E F G) := by
      unfold tripleLeftProjection
      rw [whiskerLeft_comp]
      infer_instance
    apply (cancel_epi (M ◁ tripleLeftProjection M E F G)).1
    have hl := IsModHom.smul_hom (A := M) (f := (tripleLeftModuleHom M E F G).hom)
    rw [tripleLeftModuleHom_hom] at hl
    change γ[M,(tensorRightObj M (tensorRightObj M E F.X) G.X).X] ≫
        tripleLeftProjection M E F G =
      M ◁ tripleLeftProjection M E F G ≫
        γ[M,(moduleObj M (moduleObj M E F) G).X] at hl
    let seed := tensorRightAssociator M E F.X G.X ≫ tripleRightModuleHom M E F G
    have hs := IsModHom.smul_hom (A := M) (f := seed.hom)
    change γ[M,(tensorRightObj M (tensorRightObj M E F.X) G.X).X] ≫
        ((α_ E.X F.X G.X).hom ≫ (tripleRightModuleHom M E F G).hom) =
      M ◁ ((α_ E.X F.X G.X).hom ≫ (tripleRightModuleHom M E F G).hom) ≫
        γ[M,(moduleObj M E (moduleObj M F G)).X] at hs
    rw [tripleRightModuleHom_hom] at hs
    change M ◁ tripleLeftProjection M E F G ≫
        γ[M,(moduleObj M (moduleObj M E F) G).X] ≫ associatorHom M E F G =
      M ◁ tripleLeftProjection M E F G ≫ M ◁ associatorHom M E F G ≫
        γ[M,(moduleObj M E (moduleObj M F G)).X]
    rw [← Category.assoc, ← hl, Category.assoc, tripleLeftProjection_associatorHom,
      ← whiskerLeft_comp_assoc, tripleLeftProjection_associatorHom]
    exact hs)

/-- 反復釣り合いテンソル積の加群としての結合同型。 -/
def associatorIso (E F G : Mod C M) :
    moduleObj M (moduleObj M E F) G ≅ moduleObj M E (moduleObj M F G) := by
  let i := associatorUnderlyingIso M E F G
  letI : ModObj M (obj M (moduleObj M E F) G) := (moduleObj M (moduleObj M E F) G).mod
  letI : ModObj M (obj M E (moduleObj M F G)) := (moduleObj M E (moduleObj M F G)).mod
  have : IsModHom M i.hom := (associatorModuleHom M E F G).isModHom
  have : IsModHom M i.inv := inferInstance
  exact {
    hom := associatorModuleHom M E F G
    inv := Mod.Hom.mk' i.inv IsModHom.smul_hom
    hom_inv_id := Mod.hom_ext _ _ i.hom_inv_id
    inv_hom_id := Mod.hom_ext _ _ i.inv_hom_id }

/-- 加群としての結合同型の順方向の基礎射。 -/
lemma associatorIso_hom (E F G : Mod C M) :
    (associatorIso M E F G).hom.hom = associatorHom M E F G := rfl

/-- 加群としての結合同型の逆方向の基礎射。 -/
lemma associatorIso_inv (E F G : Mod C M) :
    (associatorIso M E F G).inv.hom = associatorInv M E F G := rfl

/-- 結合同型は三つの加群の射に関して自然。 -/
lemma associator_naturality {E E' F F' G G' : Mod C M}
    (f : E ⟶ E') (g : F ⟶ F') (h : G ⟶ G') :
    moduleMap M (moduleMap M f g) h ≫ (associatorIso M E' F' G').hom =
      (associatorIso M E F G).hom ≫ moduleMap M f (moduleMap M g h) := by
  apply Mod.hom_ext
  apply (cancel_epi (tripleLeftProjection M E F G)).1
  change tripleLeftProjection M E F G ≫ map M (moduleMap M f g) h ≫
      associatorHom M E' F' G' =
    tripleLeftProjection M E F G ≫ associatorHom M E F G ≫ map M f (moduleMap M g h)
  rw [tripleLeftProjection_map_assoc, tripleLeftProjection_associatorHom,
    tripleLeftProjection_associatorHom_assoc, tripleRightProjection_map]
  rw [CategoryTheory.MonoidalCategory.associator_naturality_assoc]

/-- 三つの入力の組を右結合へ並べ直す関手。 -/
def tripleReassociate : (Mod C M × Mod C M) × Mod C M ⥤ Mod C M × (Mod C M × Mod C M) where
  obj EFG := (EFG.1.1, (EFG.1.2, EFG.2))
  map fgh := (fgh.1.1, (fgh.1.2, fgh.2))

/-- 左結合した釣り合いテンソル積の三変数関手。 -/
def tripleLeftFunctor : (Mod C M × Mod C M) × Mod C M ⥤ Mod C M :=
  (moduleBifunctor M).prod (𝟭 (Mod C M)) ⋙ moduleBifunctor M

/-- 右結合した釣り合いテンソル積の三変数関手。 -/
def tripleRightFunctor : (Mod C M × Mod C M) × Mod C M ⥤ Mod C M :=
  tripleReassociate M ⋙ (𝟭 (Mod C M)).prod (moduleBifunctor M) ⋙ moduleBifunctor M

/-- 反復釣り合いテンソル積の三変数の結合自然同型。 -/
def associatorNatIso : tripleLeftFunctor M ≅ tripleRightFunctor M :=
  NatIso.ofComponents (fun EFG => associatorIso M EFG.1.1 EFG.1.2 EFG.2)
    (fun fgh => associator_naturality M fgh.1.1 fgh.1.2 fgh.2)

end SerrePositivity.MonoidalBalancedTensor
end

end BalancedTensorAssociator

/-! ## BalancedTensorLeftUnit（旧 SerrePositivity/CategoryTheory/Monoidal/BalancedTensorLeftUnit.lean） -/

/-! # 可換モノイド上の釣り合いテンソル積の左単位比較 -/

@[expose] public section BalancedTensorLeftUnit
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (M : C) [MonObj M]

variable [IsCommMonObj M]

/-- 正則加群の右側へ移した作用は係数の乗法に一致する。 -/
lemma rightActionMap_regular : rightActionMap M (Mod.regular M) = μ[M] := by
  change (β_ M M).hom ≫ μ[M] = μ[M]
  exact IsCommMonObj.mul_comm M

variable [HasCoequalizers C]

/-- 左作用は正則加群とのテンソル積の釣り合い条件を満たす。 -/
def leftUnitBalanced (E : Mod C M) : BalancedMap M (Mod.regular M) E E.X :=
  ⟨γ[M,E.X], by
    change rightActionMap M (Mod.regular M) ▷ E.X ≫ γ[M,E.X] =
      ((α_ M M E.X).hom ≫ M ◁ γ[M,E.X]) ≫ γ[M,E.X]
    rw [rightActionMap_regular, Category.assoc]
    exact ModObj.mul_smul_self M E.X⟩

/-- 正則加群との左テンソル積から元の加群の基礎対象への射。 -/
def leftUnitHom (E : Mod C M) : obj M (Mod.regular M) E ⟶ E.X :=
  desc M (leftUnitBalanced M E)

/-- 係数の単位から得られる左単位比較の逆射。 -/
def leftUnitInv (E : Mod C M) : E.X ⟶ obj M (Mod.regular M) E :=
  (λ_ E.X).inv ≫ η[M] ▷ E.X ≫ projection M (Mod.regular M) E

/-- 左単位比較の順方向は標準射上で左作用に一致する。 -/
@[reassoc (attr := simp)] lemma projection_leftUnitHom (E : Mod C M) :
    projection M (Mod.regular M) E ≫ leftUnitHom M E = γ[M,E.X] :=
  projection_desc M _

/-- 左単位比較の逆射と順方向の合成は恒等射。 -/
lemma leftUnitInv_hom (E : Mod C M) : leftUnitInv M E ≫ leftUnitHom M E = 𝟙 E.X := by
  rw [leftUnitInv, Category.assoc, Category.assoc, projection_leftUnitHom,
    ModObj.one_smul_self, Iso.inv_hom_id]

/-- 左単位比較の順方向と逆射の合成は商上の恒等射。 -/
lemma leftUnitHom_inv (E : Mod C M) :
    leftUnitHom M E ≫ leftUnitInv M E = 𝟙 (obj M (Mod.regular M) E) := by
  apply hom_ext M
  rw [projection_leftUnitHom_assoc, leftUnitInv]
  slice_lhs 1 2 => rw [leftUnitor_inv_naturality]
  slice_lhs 2 3 => rw [whisker_exchange]
  have hc : M ◁ γ[M,E.X] ≫ projection M (Mod.regular M) E =
      (α_ M M E.X).inv ≫ μ[M] ▷ E.X ≫ projection M (Mod.regular M) E := by
    have h := projection_condition M (Mod.regular M) E
    change rightActionMap M (Mod.regular M) ▷ E.X ≫ projection M (Mod.regular M) E =
      ((α_ M M E.X).hom ≫ M ◁ γ[M,E.X]) ≫ projection M (Mod.regular M) E at h
    rw [rightActionMap_regular, Category.assoc] at h
    rw [h, Iso.inv_hom_id_assoc]
  slice_lhs 3 4 => rw [hc]
  dsimp only [Mod.regular]
  change (λ_ (M ⊗ E.X)).inv ≫ η[M] ▷ (M ⊗ E.X) ≫
      (α_ M M E.X).inv ≫ μ[M] ▷ E.X ≫ projection M (Mod.regular M) E = _
  slice_lhs 2 3 => rw [associator_inv_naturality_left]
  slice_lhs 3 4 => rw [← comp_whiskerRight, MonObj.one_mul]
  rw [Category.comp_id]
  have h : (λ_ (M ⊗ E.X)).inv ≫ (α_ (𝟙_ C) M E.X).inv ≫ (λ_ M).hom ▷ E.X =
      𝟙 (M ⊗ E.X) := by monoidal
  simpa only [Category.assoc, Category.id_comp, Mod.regular] using
    congrArg (fun k => k ≫ projection M (Mod.regular M) E) h

/-- 正則加群との左テンソル積の基礎対象の単位同型。 -/
def leftUnitUnderlyingIso (E : Mod C M) : obj M (Mod.regular M) E ≅ E.X where
  hom := leftUnitHom M E
  inv := leftUnitInv M E
  hom_inv_id := leftUnitHom_inv M E
  inv_hom_id := leftUnitInv_hom M E

variable [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]

/-- 正則加群との左テンソル積の左作用を、加群の射として降ろす。 -/
def leftUnitModuleHom (E : Mod C M) : moduleObj M (Mod.regular M) E ⟶ E :=
  moduleDesc M (leftUnitBalanced M E) (by
    change (α_ M M E.X).inv ≫ μ[M] ▷ E.X ≫ γ[M,E.X] =
      M ◁ γ[M,E.X] ≫ γ[M,E.X]
    exact (ModObj.mul_smul_self_flip (M := M) E.X).symm)

/-- 正則加群との左テンソル積の、加群としての単位同型。 -/
def leftUnitIso (E : Mod C M) : moduleObj M (Mod.regular M) E ≅ E := by
  let i := leftUnitUnderlyingIso M E
  letI : ModObj M (obj M (Mod.regular M) E) := (moduleObj M (Mod.regular M) E).mod
  have : IsModHom M i.hom := (leftUnitModuleHom M E).isModHom
  have : IsModHom M i.inv := inferInstance
  exact {
    hom := leftUnitModuleHom M E
    inv := Mod.Hom.mk' i.inv IsModHom.smul_hom
    hom_inv_id := Mod.hom_ext _ _ i.hom_inv_id
    inv_hom_id := Mod.hom_ext _ _ i.inv_hom_id }

/-- 正則加群との左テンソル積は、元の加群の射に関して自然。 -/
lemma leftUnit_naturality {E E' : Mod C M} (f : E ⟶ E') :
    moduleMap M (𝟙 (Mod.regular M)) f ≫ (leftUnitIso M E').hom =
      (leftUnitIso M E).hom ≫ f := by
  apply Mod.hom_ext
  apply hom_ext M
  change projection M (Mod.regular M) E ≫ map M (𝟙 (Mod.regular M)) f ≫
      leftUnitHom M E' =
    projection M (Mod.regular M) E ≫ leftUnitHom M E ≫ f.hom
  rw [projection_map_assoc, projection_leftUnitHom, projection_leftUnitHom_assoc]
  change (𝟙 M ⊗ₘ f.hom) ≫ γ[M,E'.X] = γ[M,E.X] ≫ f.hom
  rw [id_tensorHom]
  exact (IsModHom.smul_hom (A := M) (f := f.hom)).symm

/-- 左単位同型の順方向の基礎射。 -/
lemma leftUnitIso_hom (E : Mod C M) :
    (leftUnitIso M E).hom.hom = leftUnitHom M E := rfl

/-- 左単位同型の逆方向の基礎射。 -/
lemma leftUnitIso_inv (E : Mod C M) :
    (leftUnitIso M E).inv.hom = leftUnitInv M E := rfl

/-- 正則加群を左側に固定した釣り合いテンソル積の関手。 -/
def regularLeftTensorFunctor : Mod C M ⥤ Mod C M where
  obj E := moduleObj M (Mod.regular M) E
  map f := moduleMap M (𝟙 (Mod.regular M)) f
  map_id E := Mod.hom_ext _ _ (map_id M (Mod.regular M) E)
  map_comp f g := by
    apply Mod.hom_ext
    change map M (𝟙 (Mod.regular M)) (f ≫ g) =
      map M (𝟙 (Mod.regular M)) f ≫ map M (𝟙 (Mod.regular M)) g
    simpa only [Category.id_comp] using
      map_comp M (𝟙 (Mod.regular M)) (𝟙 (Mod.regular M)) f g

/-- 正則加群を左側に固定したテンソル積は恒等関手と自然同型。 -/
def leftUnitNatIso : regularLeftTensorFunctor M ≅ 𝟭 (Mod C M) :=
  NatIso.ofComponents (leftUnitIso M) (fun f => leftUnit_naturality M f)

end SerrePositivity.MonoidalBalancedTensor
end

end BalancedTensorLeftUnit

/-! ## BalancedTensorRightUnit（旧 SerrePositivity/CategoryTheory/Monoidal/BalancedTensorRightUnit.lean） -/

/-! # 可換モノイド上の釣り合いテンソル積の右単位比較 -/

@[expose] public section BalancedTensorRightUnit
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (M : C) [MonObj M]

/-- 右側へ移した作用の単位則。 -/
@[reassoc] lemma rightActionMap_one (E : Mod C M) :
    E.X ◁ η[M] ≫ rightActionMap M E = (ρ_ E.X).hom := by
  rw [rightActionMap, BraidedCategory.braiding_naturality_right_assoc,
    ModObj.one_smul_self, braiding_leftUnitor]

variable [IsCommMonObj M]

/-- 可換係数では右側へ移した作用が右作用の結合則を満たす。 -/
@[reassoc] lemma rightActionMap_assoc (E : Mod C M) :
    rightActionMap M E ▷ M ≫ rightActionMap M E =
      (α_ E.X M M).hom ≫ E.X ◁ μ[M] ≫ rightActionMap M E := by
  have h := action_middle M E
  simp only [rightActionMap, whiskerLeft_comp, Category.assoc] at h
  simp only [rightActionMap, comp_whiskerRight, Category.assoc]
  rw [h]
  have he : M ◁ γ[M,E.X] ≫ γ[M,E.X] =
      (α_ M M E.X).inv ≫ μ[M] ▷ E.X ≫ γ[M,E.X] :=
    ModObj.mul_smul_self_flip (M := M) E.X
  rw [he, ← BraidedCategory.hexagon_forward_assoc, Iso.hom_inv_id_assoc,
    ← BraidedCategory.braiding_naturality_right_assoc]

variable [HasCoequalizers C]

/-- 右作用は正則加群とのテンソル積の釣り合い条件を満たす。 -/
def rightUnitBalanced (E : Mod C M) : BalancedMap M E (Mod.regular M) E.X :=
  ⟨rightActionMap M E, by
    change rightActionMap M E ▷ M ≫ rightActionMap M E =
      ((α_ E.X M M).hom ≫ E.X ◁ μ[M]) ≫ rightActionMap M E
    rw [Category.assoc, rightActionMap_assoc]⟩

/-- 正則加群との右テンソル積から元の加群の基礎対象への射。 -/
def rightUnitHom (E : Mod C M) : obj M E (Mod.regular M) ⟶ E.X :=
  desc M (rightUnitBalanced M E)

/-- 係数の単位から得られる右単位比較の逆射。 -/
def rightUnitInv (E : Mod C M) : E.X ⟶ obj M E (Mod.regular M) :=
  (ρ_ E.X).inv ≫ E.X ◁ η[M] ≫ projection M E (Mod.regular M)

/-- 右単位比較の順方向は標準射上で右作用に一致する。 -/
@[reassoc (attr := simp)] lemma projection_rightUnitHom (E : Mod C M) :
    projection M E (Mod.regular M) ≫ rightUnitHom M E = rightActionMap M E :=
  projection_desc M _

/-- 右単位比較の逆射と順方向の合成は恒等射。 -/
lemma rightUnitInv_hom (E : Mod C M) : rightUnitInv M E ≫ rightUnitHom M E = 𝟙 E.X := by
  rw [rightUnitInv, Category.assoc, Category.assoc, projection_rightUnitHom,
    rightActionMap_one, Iso.inv_hom_id]

/-- 右単位比較の順方向と逆射の合成は商上の恒等射。 -/
lemma rightUnitHom_inv (E : Mod C M) :
    rightUnitHom M E ≫ rightUnitInv M E = 𝟙 (obj M E (Mod.regular M)) := by
  apply hom_ext M
  rw [projection_rightUnitHom_assoc, rightUnitInv]
  slice_lhs 1 2 => rw [rightUnitor_inv_naturality]
  slice_lhs 2 3 => rw [← whisker_exchange]
  have hc : rightActionMap M E ▷ M ≫ projection M E (Mod.regular M) =
      ((α_ E.X M M).hom ≫ E.X ◁ μ[M]) ≫ projection M E (Mod.regular M) :=
    projection_condition M E (Mod.regular M)
  slice_lhs 3 4 => rw [hc]
  simp only [Category.assoc]
  change (ρ_ (E.X ⊗ M)).inv ≫ (E.X ⊗ M) ◁ η[M] ≫
      (α_ E.X M M).hom ≫ E.X ◁ μ[M] ≫ projection M E (Mod.regular M) = _
  slice_lhs 2 3 => rw [associator_naturality_right]
  slice_lhs 3 4 => rw [← whiskerLeft_comp, MonObj.mul_one]
  rw [Category.comp_id]
  have h : (ρ_ (E.X ⊗ M)).inv ≫ (α_ E.X M (𝟙_ C)).hom ≫ E.X ◁ (ρ_ M).hom =
      𝟙 (E.X ⊗ M) := by monoidal
  simpa only [Category.assoc, Category.id_comp] using
    congrArg (fun k => k ≫ projection M E (Mod.regular M)) h

/-- 正則加群との右テンソル積の基礎対象の単位同型。 -/
def rightUnitUnderlyingIso (E : Mod C M) : obj M E (Mod.regular M) ≅ E.X where
  hom := rightUnitHom M E
  inv := rightUnitInv M E
  hom_inv_id := rightUnitHom_inv M E
  inv_hom_id := rightUnitInv_hom M E

variable [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]

/-- 正則加群との右テンソル積の右作用を、加群の射として降ろす。 -/
def rightUnitModuleHom (E : Mod C M) : moduleObj M E (Mod.regular M) ⟶ E :=
  moduleDesc M (rightUnitBalanced M E) (by
    change (α_ M E.X M).inv ≫ γ[M,E.X] ▷ M ≫ rightActionMap M E =
      M ◁ rightActionMap M E ≫ γ[M,E.X]
    rw [action_middle, Iso.inv_hom_id_assoc])

/-- 正則加群との右テンソル積の、加群としての単位同型。 -/
def rightUnitIso (E : Mod C M) : moduleObj M E (Mod.regular M) ≅ E := by
  let i := rightUnitUnderlyingIso M E
  letI : ModObj M (obj M E (Mod.regular M)) := (moduleObj M E (Mod.regular M)).mod
  have : IsModHom M i.hom := (rightUnitModuleHom M E).isModHom
  have : IsModHom M i.inv := inferInstance
  exact {
    hom := rightUnitModuleHom M E
    inv := Mod.Hom.mk' i.inv IsModHom.smul_hom
    hom_inv_id := Mod.hom_ext _ _ i.hom_inv_id
    inv_hom_id := Mod.hom_ext _ _ i.inv_hom_id }

/-- 正則加群との右テンソル積は、元の加群の射に関して自然。 -/
lemma rightUnit_naturality {E E' : Mod C M} (f : E ⟶ E') :
    moduleMap M f (𝟙 (Mod.regular M)) ≫ (rightUnitIso M E').hom =
      (rightUnitIso M E).hom ≫ f := by
  apply Mod.hom_ext
  apply hom_ext M
  change projection M E (Mod.regular M) ≫ map M f (𝟙 (Mod.regular M)) ≫
      rightUnitHom M E' =
    projection M E (Mod.regular M) ≫ rightUnitHom M E ≫ f.hom
  rw [projection_map_assoc, projection_rightUnitHom, projection_rightUnitHom_assoc]
  change (f.hom ⊗ₘ 𝟙 M) ≫ rightActionMap M E' = rightActionMap M E ≫ f.hom
  rw [tensorHom_id, rightActionMap_naturality]

/-- 右単位同型の順方向の基礎射。 -/
lemma rightUnitIso_hom (E : Mod C M) :
    (rightUnitIso M E).hom.hom = rightUnitHom M E := rfl

/-- 右単位同型の逆方向の基礎射。 -/
lemma rightUnitIso_inv (E : Mod C M) :
    (rightUnitIso M E).inv.hom = rightUnitInv M E := rfl

/-- 正則加群を右側に固定した釣り合いテンソル積の関手。 -/
def regularRightTensorFunctor : Mod C M ⥤ Mod C M where
  obj E := moduleObj M E (Mod.regular M)
  map f := moduleMap M f (𝟙 (Mod.regular M))
  map_id E := Mod.hom_ext _ _ (map_id M E (Mod.regular M))
  map_comp f g := by
    apply Mod.hom_ext
    change map M (f ≫ g) (𝟙 (Mod.regular M)) =
      map M f (𝟙 (Mod.regular M)) ≫ map M g (𝟙 (Mod.regular M))
    simpa only [Category.id_comp] using
      map_comp M f g (𝟙 (Mod.regular M)) (𝟙 (Mod.regular M))

/-- 正則加群を右側に固定したテンソル積は恒等関手と自然同型。 -/
def rightUnitNatIso : regularRightTensorFunctor M ≅ 𝟭 (Mod C M) :=
  NatIso.ofComponents (rightUnitIso M) (fun f => rightUnit_naturality M f)

end SerrePositivity.MonoidalBalancedTensor
end

end BalancedTensorRightUnit

/-! ## BalancedTensorPentagon（旧 SerrePositivity/CategoryTheory/Monoidal/BalancedTensorPentagon.lean） -/

/-! # 釣り合いテンソル積のpentagon整合性 -/

@[expose] public section BalancedTensorPentagon
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (M : C) [MonObj M] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

/-- 四因子を全て左結合した商への標準射。 -/
def quadrupleLeftProjection (E F G H : Mod C M) :
    ((E.X ⊗ F.X) ⊗ G.X) ⊗ H.X ⟶ obj M (moduleObj M (moduleObj M E F) G) H :=
  tripleLeftProjection M E F G ▷ H.X ≫ projection M (moduleObj M (moduleObj M E F) G) H

/-- 四因子を全て右結合した商への標準射。 -/
def quadrupleRightProjection (E F G H : Mod C M) :
    E.X ⊗ (F.X ⊗ (G.X ⊗ H.X)) ⟶ obj M E (moduleObj M F (moduleObj M G H)) :=
  E.X ◁ tripleRightProjection M F G H ≫ projection M E (moduleObj M F (moduleObj M G H))

/-- 二つずつ組にした四因子の商への標準射。 -/
def quadrupleMiddleProjection (E F G H : Mod C M) :
    (E.X ⊗ F.X) ⊗ (G.X ⊗ H.X) ⟶ obj M (moduleObj M E F) (moduleObj M G H) :=
  (projection M E F ⊗ₘ projection M G H) ≫
    projection M (moduleObj M E F) (moduleObj M G H)

/-- pentagonの上側の中間の結合順への標準射。 -/
def pentagonUpperProjection (E F G H : Mod C M) :
    (E.X ⊗ (F.X ⊗ G.X)) ⊗ H.X ⟶ obj M (moduleObj M E (moduleObj M F G)) H :=
  (E.X ◁ projection M F G) ▷ H.X ≫ tripleLeftProjection M E (moduleObj M F G) H

/-- pentagonの下側の中間の結合順への標準射。 -/
def pentagonLowerProjection (E F G H : Mod C M) :
    E.X ⊗ ((F.X ⊗ G.X) ⊗ H.X) ⟶ obj M E (moduleObj M (moduleObj M F G) H) :=
  E.X ◁ tripleLeftProjection M F G H ≫ projection M E (moduleObj M (moduleObj M F G) H)

/-- 左結合した四因子の標準射はエピ射。 -/
instance quadrupleLeftProjection_epi (E F G H : Mod C M) :
    Epi (quadrupleLeftProjection M E F G H) := by
  have : Epi ((projection M E F ▷ G.X) ▷ H.X) := inferInstanceAs
    (Epi (((tensorRight G.X) ⋙ tensorRight H.X).map
      (coequalizer.π (relationLeft M E F) (relationRight M E F))))
  unfold quadrupleLeftProjection tripleLeftProjection
  rw [comp_whiskerRight]
  infer_instance

/-- 上側の第一の結合変更の標準射上の計算。 -/
@[reassoc] lemma quadrupleLeftProjection_map_associator (E F G H : Mod C M) :
    quadrupleLeftProjection M E F G H ≫ map M (associatorIso M E F G).hom (𝟙 H) =
      (α_ E.X F.X G.X).hom ▷ H.X ≫ pentagonUpperProjection M E F G H := by
  rw [quadrupleLeftProjection, Category.assoc, projection_map]
  change tripleLeftProjection M E F G ▷ H.X ≫
    (associatorHom M E F G ⊗ₘ 𝟙 H.X) ≫ projection M (moduleObj M E (moduleObj M F G)) H = _
  rw [tensorHom_id, ← comp_whiskerRight_assoc, tripleLeftProjection_associatorHom,
    comp_whiskerRight]
  simp only [tripleRightProjection, comp_whiskerRight, pentagonUpperProjection,
    tripleLeftProjection, Category.assoc]

/-- 上側の第二の結合変更の標準射上の計算。 -/
@[reassoc] lemma pentagonUpperProjection_associator (E F G H : Mod C M) :
    pentagonUpperProjection M E F G H ≫ associatorHom M E (moduleObj M F G) H =
      (α_ E.X (F.X ⊗ G.X) H.X).hom ≫ pentagonLowerProjection M E F G H := by
  rw [pentagonUpperProjection, Category.assoc, tripleLeftProjection_associatorHom]
  erw [associator_naturality_middle_assoc]
  simp only [tripleRightProjection, pentagonLowerProjection, tripleLeftProjection,
    whiskerLeft_comp, Category.assoc]

/-- 上側の第三の結合変更の標準射上の計算。 -/
@[reassoc] lemma pentagonLowerProjection_map_associator (E F G H : Mod C M) :
    pentagonLowerProjection M E F G H ≫ map M (𝟙 E) (associatorIso M F G H).hom =
      E.X ◁ (α_ F.X G.X H.X).hom ≫ quadrupleRightProjection M E F G H := by
  rw [pentagonLowerProjection, Category.assoc, projection_map]
  change E.X ◁ tripleLeftProjection M F G H ≫
    (𝟙 E.X ⊗ₘ associatorHom M F G H) ≫ projection M E (moduleObj M F (moduleObj M G H)) = _
  rw [id_tensorHom, ← whiskerLeft_comp_assoc, tripleLeftProjection_associatorHom,
    whiskerLeft_comp]
  simp only [quadrupleRightProjection, Category.assoc]

/-- 下側の第一の結合変更の標準射上の計算。 -/
@[reassoc] lemma quadrupleLeftProjection_associator (E F G H : Mod C M) :
    quadrupleLeftProjection M E F G H ≫ associatorHom M (moduleObj M E F) G H =
      (α_ (E.X ⊗ F.X) G.X H.X).hom ≫ quadrupleMiddleProjection M E F G H := by
  simp only [quadrupleLeftProjection, tripleLeftProjection, comp_whiskerRight, Category.assoc]
  rw [associatorHom, projection_desc, projection_associatorStep]
  erw [associator_naturality_left_assoc]
  simp only [tripleRightProjection, quadrupleMiddleProjection, tensorHom_def, Category.assoc,
    moduleObj_underlying]

/-- 下側の第二の結合変更の標準射上の計算。 -/
@[reassoc] lemma quadrupleMiddleProjection_associator (E F G H : Mod C M) :
    quadrupleMiddleProjection M E F G H ≫ associatorHom M E F (moduleObj M G H) =
      (α_ E.X F.X (G.X ⊗ H.X)).hom ≫ quadrupleRightProjection M E F G H := by
  simp only [quadrupleMiddleProjection, tensorHom_def, Category.assoc]
  rw [← whisker_exchange_assoc]
  rw [associatorHom, projection_desc]
  change (E.X ⊗ F.X) ◁ projection M G H ≫
    projection M E F ▷ (moduleObj M G H).X ≫ associatorStep M E F (moduleObj M G H) = _
  rw [projection_associatorStep]
  erw [associator_naturality_right_assoc]
  simp only [tripleRightProjection, quadrupleRightProjection, whiskerLeft_comp, Category.assoc]

/-- 釣り合いテンソル積の結合同型はpentagon整合性を満たす。 -/
lemma pentagon (E F G H : Mod C M) :
    moduleMap M (associatorIso M E F G).hom (𝟙 H) ≫
        (associatorIso M E (moduleObj M F G) H).hom ≫
          moduleMap M (𝟙 E) (associatorIso M F G H).hom =
      (associatorIso M (moduleObj M E F) G H).hom ≫
        (associatorIso M E F (moduleObj M G H)).hom := by
  apply Mod.hom_ext
  apply (cancel_epi (quadrupleLeftProjection M E F G H)).1
  change quadrupleLeftProjection M E F G H ≫
      map M (associatorIso M E F G).hom (𝟙 H) ≫ associatorHom M E (moduleObj M F G) H ≫
        map M (𝟙 E) (associatorIso M F G H).hom =
    quadrupleLeftProjection M E F G H ≫ associatorHom M (moduleObj M E F) G H ≫
      associatorHom M E F (moduleObj M G H)
  rw [quadrupleLeftProjection_map_associator_assoc, pentagonUpperProjection_associator_assoc,
    pentagonLowerProjection_map_associator, quadrupleLeftProjection_associator_assoc,
    quadrupleMiddleProjection_associator, MonoidalCategory.pentagon_assoc]

end SerrePositivity.MonoidalBalancedTensor
end

end BalancedTensorPentagon

/-! ## BalancedTensorTriangle（旧 SerrePositivity/CategoryTheory/Monoidal/BalancedTensorTriangle.lean） -/

/-! # 釣り合いテンソル積のtriangle整合性 -/

@[expose] public section BalancedTensorTriangle
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (M : C) [MonObj M] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

/-- 結合同型を左単位比較へ続ける経路と、右単位比較を先に行う経路は一致する。 -/
lemma triangle (E F : Mod C M) :
    (associatorIso M E (Mod.regular M) F).hom ≫
        moduleMap M (𝟙 E) (leftUnitIso M F).hom =
      moduleMap M (rightUnitIso M E).hom (𝟙 F) := by
  apply Mod.hom_ext
  apply (cancel_epi (tripleLeftProjection M E (Mod.regular M) F)).1
  change tripleLeftProjection M E (Mod.regular M) F ≫
      associatorHom M E (Mod.regular M) F ≫ map M (𝟙 E) (leftUnitIso M F).hom =
    tripleLeftProjection M E (Mod.regular M) F ≫ map M (rightUnitIso M E).hom (𝟙 F)
  rw [tripleLeftProjection_associatorHom_assoc, tripleRightProjection, Category.assoc,
    projection_map, tripleLeftProjection, Category.assoc, projection_map]
  change (α_ E.X M F.X).hom ≫ E.X ◁ projection M (Mod.regular M) F ≫
      (𝟙 E.X ⊗ₘ leftUnitHom M F) ≫ projection M E F =
    projection M E (Mod.regular M) ▷ F.X ≫
      (rightUnitHom M E ⊗ₘ 𝟙 F.X) ≫ projection M E F
  rw [id_tensorHom, tensorHom_id, ← whiskerLeft_comp_assoc, projection_leftUnitHom,
    ← comp_whiskerRight_assoc, projection_rightUnitHom]
  simpa only [relationLeft, relationRight, Category.assoc] using
    (projection_condition M E F).symm

/-- triangleの両経路を、元の結合順から逆結合同型を介した比較として書く。 -/
lemma triangle_inv (E F : Mod C M) :
    (associatorIso M E (Mod.regular M) F).inv ≫
        moduleMap M (rightUnitIso M E).hom (𝟙 F) =
      moduleMap M (𝟙 E) (leftUnitIso M F).hom := by
  rw [← triangle M E F, Iso.inv_hom_id_assoc]

end SerrePositivity.MonoidalBalancedTensor
end

end BalancedTensorTriangle

/-! ## BalancedTensorMonoidal（旧 SerrePositivity/CategoryTheory/Monoidal/BalancedTensorMonoidal.lean） -/

/-! # 可換モノイド上の内部加群のモノイダル構造 -/

@[expose] public section BalancedTensorMonoidal
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (M : C) [MonObj M] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

/-- 釣り合いテンソル積、正則加群と構成済みの比較同型によるモノイダル構造のデータ。 -/
instance monoidalCategoryStruct : MonoidalCategoryStruct (Mod C M) where
  tensorObj := moduleObj M
  tensorHom := moduleMap M
  whiskerLeft E {_ _} f := moduleMap M (𝟙 E) f
  whiskerRight {_ _} f F := moduleMap M f (𝟙 F)
  tensorUnit := Mod.regular M
  associator := associatorIso M
  leftUnitor := leftUnitIso M
  rightUnitor := rightUnitIso M

/-- 釣り合いテンソル積は可換モノイド上の内部加群圏をモノイダル圏にする。 -/
instance monoidalCategory : MonoidalCategory (Mod C M) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun E F => Mod.hom_ext _ _ (map_id M E F))
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := fun f g f' g' =>
      Mod.hom_ext _ _ (map_comp M f f' g g').symm)
    (associator_naturality := fun f g h => associator_naturality M f g h)
    (leftUnitor_naturality := fun f => leftUnit_naturality M f)
    (rightUnitor_naturality := fun f => rightUnit_naturality M f)
    (pentagon := pentagon M)
    (triangle := triangle M)

end SerrePositivity.MonoidalBalancedTensor
end

end BalancedTensorMonoidal

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.4.3.12" (partial := special) "仮定：余等化子とそれを保つ左右テンソルをもつ通常のモノイダル圏（内部左加群の構成には組紐と可換モノイドも仮定）（Lean が強い：通常のモノイダル圏と指定した余等化子の存在）。結論：双圏の A の自己射圏は相対テンソルを積とするモノイダル圏となる（この仮定での HA の結論の一部に一致）。可換な場合は内部加群の平衡テンソルによる構造も構成済み。∞ オペラッドの比較は含まれない。"] _root_.SerrePositivity.MonoidalBalancedTensor.monoidalCategory
