module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.CategoryTheory.Monoidal.Mod.BalancedTensor
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import SerrePositivity.CategoryTheory.Monoidal.Mod.Monoidal

/-!
# Monoidal.Mod.InternalHom

## 概要
加群の内部 Hom、その作用、閉構造と関手性をまとめる。各構成の詳細は以下の元モジュールの説明を参照。

## 方針
元の宣言と証明を保持し、依存順に section を分けて配置する。

## 規約
公開宣言名・名前空間・宇宙変数の意味を変更しない。元の module docstring は各節に保存する。

## 使われ方
旧モジュールの利用元は `SerrePositivity.CategoryTheory.Monoidal.Mod.InternalHom` を直接 import する。
-/

/-! ## ModuleInternalHom（旧 SerrePositivity/CategoryTheory/Monoidal/ModuleInternalHom.lean） -/

/-! # 内部加群の内部Homの基礎対象

作用との両立を表す二つの射の等化子と、パラメータ付き線形射の普遍性を構成する。
この段階では等化子上の加群作用は構成しない。
-/

@[expose] public section ModuleInternalHom
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalModuleInternalHom

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  (M : C) [MonObj M] (E F : Mod C M)

/-- 第一変数の作用による制限。 -/
def sourceAction : (E.X ⟶[C] F.X) ⟶ ((M ⊗ E.X) ⟶[C] F.X) :=
  (pre γ[M, E.X]).app F.X

/-- 評価後に値域の作用を施す射の随伴転置。 -/
def targetAction : (E.X ⟶[C] F.X) ⟶ ((M ⊗ E.X) ⟶[C] F.X) :=
  curry ((α_ M E.X (E.X ⟶[C] F.X)).hom ≫
    M ◁ (ihom.ev E.X).app F.X ≫ γ[M, F.X])

/-- パラメータ付き射が第一変数の作用と両立する条件。 -/
def Linear {X : C} (f : E.X ⊗ X ⟶ F.X) : Prop :=
  γ[M, E.X] ▷ X ≫ f = (α_ M E.X X).hom ≫ M ◁ f ≫ γ[M, F.X]

/-- 線形性は内部Homの二つの作用射の等化条件に一致する。 -/
lemma curry_condition {X : C} (f : E.X ⊗ X ⟶ F.X) :
    curry f ≫ sourceAction M E F = curry f ≫ targetAction M E F ↔ Linear M E F f := by
  rw [sourceAction, curry_pre_app]
  rw [targetAction, ← curry_natural_left]
  rw [curry_injective.eq_iff]
  simp only [Linear, associator_naturality_right_assoc]
  rw [← whiskerLeft_comp_assoc, whiskerLeft_curry_ihom_ev_app]

variable [HasEqualizers C]

/-- 加群の内部Homの基礎対象。 -/
def obj : C := equalizer (sourceAction M E F) (targetAction M E F)

/-- 通常の内部Homへの等化子の標準射。 -/
def inclusion : obj M E F ⟶ (E.X ⟶[C] F.X) := equalizer.ι _ _

instance inclusion_mono : Mono (inclusion M E F) := inferInstanceAs (Mono (equalizer.ι _ _))

@[reassoc]
lemma inclusion_condition : inclusion M E F ≫ sourceAction M E F =
    inclusion M E F ≫ targetAction M E F := equalizer.condition _ _

/-- 等化子をパラメータとする評価射。 -/
def evaluation : E.X ⊗ obj M E F ⟶ F.X := uncurry (inclusion M E F)

lemma evaluation_linear : Linear M E F (evaluation M E F) := by
  apply (curry_condition M E F _).mp
  simpa only [evaluation, curry_uncurry] using inclusion_condition M E F

/-- パラメータ付き線形射を等化子へ転置する。 -/
def lift {X : C} (f : E.X ⊗ X ⟶ F.X) (hf : Linear M E F f) : X ⟶ obj M E F :=
  equalizer.lift (curry f) ((curry_condition M E F f).mpr hf)

@[reassoc (attr := simp)]
lemma lift_inclusion {X : C} (f : E.X ⊗ X ⟶ F.X) (hf : Linear M E F f) :
    lift M E F f hf ≫ inclusion M E F = curry f := equalizer.lift_ι _ _

@[reassoc (attr := simp)]
lemma lift_evaluation {X : C} (f : E.X ⊗ X ⟶ F.X) (hf : Linear M E F f) :
    E.X ◁ lift M E F f hf ≫ evaluation M E F = f := by
  rw [evaluation, ← uncurry_natural_left, lift_inclusion, uncurry_curry]

lemma hom_ext {X : C} {f g : X ⟶ obj M E F}
    (h : f ≫ inclusion M E F = g ≫ inclusion M E F) : f = g :=
  (cancel_mono (inclusion M E F)).mp h

/-- 任意の等化子への射が与える評価は線形。 -/
lemma uncurry_linear {X : C} (f : X ⟶ obj M E F) :
    Linear M E F (uncurry (f ≫ inclusion M E F)) := by
  apply (curry_condition M E F _).mp
  simp only [curry_uncurry, Category.assoc, inclusion_condition]

/-- 等化子への射とパラメータ付き線形射の全単射。 -/
def homEquiv (X : C) : (X ⟶ obj M E F) ≃
    {f : E.X ⊗ X ⟶ F.X // Linear M E F f} where
  toFun f := ⟨uncurry (f ≫ inclusion M E F), uncurry_linear M E F f⟩
  invFun f := lift M E F f.val f.property
  left_inv f := by
    apply hom_ext M E F
    simp only [lift_inclusion, curry_uncurry]
  right_inv f := by
    apply Subtype.ext
    simp only [lift_inclusion, uncurry_curry]

/-- 右テンソル加群からの加群射を等化子へ転置する。 -/
def moduleLift {X : C} (f : MonoidalBalancedTensor.tensorRightObj M E X ⟶ F) :
    X ⟶ obj M E F :=
  lift M E F f.hom (by
    have h := IsModHom.smul_hom (A := M) (f := f.hom)
    change ((α_ M E.X X).inv ≫ γ[M, E.X] ▷ X) ≫ f.hom =
      M ◁ f.hom ≫ γ[M, F.X] at h
    simp only [Category.assoc] at h
    unfold Linear
    rw [← h]
    simp)

/-- 等化子への射を右テンソル加群からの加群射へ戻す。 -/
def moduleUnlift {X : C} (f : X ⟶ obj M E F) :
    MonoidalBalancedTensor.tensorRightObj M E X ⟶ F :=
  Mod.Hom.mk' (uncurry (f ≫ inclusion M E F)) (by
    change ((α_ M E.X X).inv ≫ γ[M, E.X] ▷ X) ≫
      uncurry (f ≫ inclusion M E F) =
        M ◁ uncurry (f ≫ inclusion M E F) ≫ γ[M, F.X]
    simp only [Category.assoc]
    rw [uncurry_linear M E F f]
    simp)

/-- 等化子は右テンソル加群からの加群射を分類する。 -/
def moduleHomEquiv (X : C) : (X ⟶ obj M E F) ≃
    (MonoidalBalancedTensor.tensorRightObj M E X ⟶ F) where
  toFun := moduleUnlift M E F
  invFun := moduleLift M E F
  left_inv f := by
    apply hom_ext M E F
    simp only [moduleLift, lift_inclusion]
    change curry (uncurry (f ≫ inclusion M E F)) = f ≫ inclusion M E F
    exact curry_uncurry _
  right_inv f := by
    apply Mod.hom_ext
    change uncurry (lift M E F f.hom _ ≫ inclusion M E F) = f.hom
    rw [lift_inclusion, uncurry_curry]

/-- 普遍性はパラメータ対象の射に関して自然。 -/
lemma moduleUnlift_naturality {X Y : C} (g : X ⟶ Y) (f : Y ⟶ obj M E F) :
    moduleUnlift M E F (g ≫ f) =
      MonoidalBalancedTensor.tensorRightMap M (𝟙 E) g ≫ moduleUnlift M E F f := by
  apply Mod.hom_ext
  change uncurry ((g ≫ f) ≫ inclusion M E F) =
    (𝟙 E.X ⊗ₘ g) ≫ uncurry (f ≫ inclusion M E F)
  rw [Category.assoc, uncurry_natural_left]
  simp

end SerrePositivity.MonoidalModuleInternalHom
end

end ModuleInternalHom

/-! ## ModuleInternalHomAction（旧 SerrePositivity/CategoryTheory/Monoidal/ModuleInternalHomAction.lean） -/

/-! # 可換係数上の内部Homの加群作用 -/

@[expose] public section ModuleInternalHomAction
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalModuleInternalHom

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CategoryTheory.MonObj
open MonoidalBalancedTensor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  (M : C) [MonObj M]

/-- 右テンソル加群の結合子の逆も加群射である。 -/
def tensorRightAssociatorInv (E : Mod C M) (X Y : C) :
    tensorRightObj M E (X ⊗ Y) ⟶ tensorRightObj M (tensorRightObj M E X) Y := by
  letI : ModObj M (E.X ⊗ (X ⊗ Y)) := (tensorRightObj M E (X ⊗ Y)).mod
  letI : ModObj M ((E.X ⊗ X) ⊗ Y) := (tensorRightObj M (tensorRightObj M E X) Y).mod
  letI : IsModHom M (α_ E.X X Y).hom := (tensorRightAssociator M E X Y).isModHom
  exact ⟨(α_ E.X X Y).inv⟩

variable [BraidedCategory C] [IsCommMonObj M] [HasEqualizers C] (E F : Mod C M)

/-- 原変数の右作用を介して評価へ送る加群射。 -/
def actionTranspose : tensorRightObj M E (M ⊗ obj M E F) ⟶ F :=
  tensorRightAssociatorInv M E M (obj M E F) ≫
    tensorRightMap M (rightActionHom M E) (𝟙 (obj M E F)) ≫
      moduleUnlift M E F (𝟙 (obj M E F))

/-- 内部Homの作用射。 -/
def action : M ⊗ obj M E F ⟶ obj M E F := moduleLift M E F (actionTranspose M E F)

omit [BraidedCategory C] [IsCommMonObj M] in
/-- 評価は内部Homの射の等式を検出する。 -/
lemma evaluation_hom_ext {X : C} {f g : X ⟶ obj M E F}
    (h : E.X ◁ f ≫ evaluation M E F = E.X ◁ g ≫ evaluation M E F) : f = g := by
  apply hom_ext M E F
  apply uncurry_injective
  simpa only [uncurry_natural_left, evaluation] using h

/-- 内部Homの作用と評価の合成公式。 -/
@[reassoc]
lemma action_evaluation : E.X ◁ action M E F ≫ evaluation M E F =
    (α_ E.X M (obj M E F)).inv ≫ rightActionMap M E ▷ obj M E F ≫
      evaluation M E F := by
  unfold action moduleLift
  rw [lift_evaluation]
  change (α_ E.X M (obj M E F)).inv ≫ (rightActionMap M E ⊗ₘ 𝟙 _) ≫
    uncurry (𝟙 _ ≫ inclusion M E F) = _
  simp only [tensorHom_id, Category.id_comp, evaluation]

/-- 内部Homの作用の単位則。 -/
lemma action_one : η[M] ▷ obj M E F ≫ action M E F = (λ_ (obj M E F)).hom := by
  apply evaluation_hom_ext M E F
  rw [whiskerLeft_comp, Category.assoc, action_evaluation]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    rightActionMap_one]
  monoidal

/-- 内部Homの作用の結合則。 -/
lemma action_mul : μ[M] ▷ obj M E F ≫ action M E F =
    (α_ M M (obj M E F)).hom ≫ M ◁ action M E F ≫ action M E F := by
  apply evaluation_hom_ext M E F
  simp only [whiskerLeft_comp, Category.assoc]
  rw [action_evaluation]
  have hr : E.X ◁ μ[M] ≫ rightActionMap M E =
      (α_ E.X M M).inv ≫ rightActionMap M E ▷ M ≫ rightActionMap M E := by
    rw [rightActionMap_assoc, Iso.inv_hom_id_assoc]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, hr]
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    action_evaluation, associator_inv_naturality_left_assoc]
  have h : (α_ E.X (M ⊗ M) (obj M E F)).inv ≫
      (α_ E.X M M).inv ▷ obj M E F =
      E.X ◁ (α_ M M (obj M E F)).hom ≫
        (α_ E.X M (M ⊗ obj M E F)).inv ≫
          (α_ (E.X ⊗ M) M (obj M E F)).inv := by monoidal
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ (rightActionMap M E ▷ M) ▷ obj M E F ≫
      rightActionMap M E ▷ obj M E F ≫ evaluation M E F) h

/-- 可換モノイド上の内部Homの加群構造。 -/
@[instance_reducible] def internalHomAction : ModObj M (obj M E F) where
  smul := action M E F
  one_smul := action_one M E F
  mul_smul := action_mul M E F

/-- 内部Homを加群対象として束ねる。 -/
def moduleObj : Mod C M :=
  letI := internalHomAction M E F
  ⟨obj M E F⟩

variable [HasCoequalizers C]

/-- 内部Homの評価は両方の加群作用に関して釣り合う。 -/
def evaluationBalanced : BalancedMap M E (moduleObj M E F) F.X :=
  ⟨evaluation M E F, by
    change rightActionMap M E ▷ obj M E F ≫ evaluation M E F =
      ((α_ E.X M (obj M E F)).hom ≫ E.X ◁ action M E F) ≫ evaluation M E F
    rw [Category.assoc, action_evaluation, Iso.hom_inv_id_assoc]⟩

variable [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]

/-- 釣り合いテンソル積から値域への加群としての評価射。 -/
def evaluationModule : MonoidalBalancedTensor.moduleObj M E (moduleObj M E F) ⟶ F :=
  moduleDesc M (evaluationBalanced M E F) (by
    change (α_ M E.X (obj M E F)).inv ≫ γ[M, E.X] ▷ obj M E F ≫
      evaluation M E F = M ◁ evaluation M E F ≫ γ[M, F.X]
    rw [evaluation_linear M E F, Iso.inv_hom_id_assoc])

/-- 商の標準射と加群としての評価の合成は元の評価。 -/
@[reassoc (attr := simp)]
lemma projection_evaluationModule : projection M E (moduleObj M E F) ≫
    (evaluationModule M E F).hom = evaluation M E F :=
  projection_desc M (evaluationBalanced M E F)

end SerrePositivity.MonoidalModuleInternalHom
end

end ModuleInternalHomAction

/-! ## ModuleClosed（旧 SerrePositivity/CategoryTheory/Monoidal/ModuleClosed.lean） -/

/-! # 可換モノイド上の加群圏の閉構造

釣り合いテンソル積からの加群射と内部Homへの加群射を自然なHom同値で比較する。
-/

@[expose] public section ModuleClosed
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalModuleInternalHom

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CategoryTheory.MonObj
open MonoidalBalancedTensor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  [BraidedCategory C] (M : C) [MonObj M] [IsCommMonObj M] [HasEqualizers C]
  [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]
  (E : Mod C M)

/-- 商からの加群射の基礎対象上の転置。 -/
def curryUnderlying {X F : Mod C M} (f : E ⊗ X ⟶ F) : X.X ⟶ obj M E F :=
  moduleLift M E F (projectionModuleHom M E X ≫ f)

/-- 基礎対象上の転置と評価の合成公式。 -/
@[reassoc (attr := simp)]
lemma curryUnderlying_evaluation {X F : Mod C M} (f : E ⊗ X ⟶ F) :
    E.X ◁ curryUnderlying M E f ≫ evaluation M E F = projection M E X ≫ f.hom := by
  unfold curryUnderlying moduleLift
  rw [lift_evaluation]
  rfl

/-- 釣り合い条件から転置の加群作用との両立が従う。 -/
def curryModule {X F : Mod C M} (f : E ⊗ X ⟶ F) : X ⟶ moduleObj M E F :=
  Mod.Hom.mk' (curryUnderlying M E f) (by
    change γ[M, X.X] ≫ curryUnderlying M E f = M ◁ curryUnderlying M E f ≫ action M E F
    apply evaluation_hom_ext M E F
    simp only [whiskerLeft_comp, Category.assoc]
    rw [curryUnderlying_evaluation, action_evaluation,
      associator_inv_naturality_right_assoc, whisker_exchange_assoc,
      curryUnderlying_evaluation]
    have h := projection_condition M E X
    change rightActionMap M E ▷ X.X ≫ projection M E X =
      ((α_ E.X M X.X).hom ≫ E.X ◁ γ[M, X.X]) ≫ projection M E X at h
    simp only [Category.assoc] at h
    rw [reassoc_of% h, Iso.inv_hom_id_assoc])

/-- 内部Homへの加群射をテンソル積からの加群射へ戻す。 -/
def uncurryModule {X F : Mod C M} (f : X ⟶ moduleObj M E F) : E ⊗ X ⟶ F :=
  moduleMap M (𝟙 E) f ≫ evaluationModule M E F

/-- 逆転置の商の標準射上での公式。 -/
@[reassoc (attr := simp)]
lemma projection_uncurryModule {X F : Mod C M} (f : X ⟶ moduleObj M E F) :
    projection M E X ≫ (uncurryModule M E f).hom = E.X ◁ f.hom ≫ evaluation M E F := by
  change projection M E X ≫ map M (𝟙 E) f ≫ (evaluationModule M E F).hom = _
  rw [projection_map_assoc, projection_evaluationModule]
  simp

/-- テンソル積からの加群射と内部Homへの加群射の全単射。 -/
def tensorHomEquiv (X F : Mod C M) : (E ⊗ X ⟶ F) ≃ (X ⟶ moduleObj M E F) where
  toFun := curryModule M E
  invFun := uncurryModule M E
  left_inv f := by
    apply Mod.hom_ext
    apply (cancel_epi (projection M E X)).mp
    rw [projection_uncurryModule]
    exact curryUnderlying_evaluation M E f
  right_inv f := by
    apply Mod.hom_ext
    apply evaluation_hom_ext M E F
    change E.X ◁ curryUnderlying M E (uncurryModule M E f) ≫ evaluation M E F = _
    rw [curryUnderlying_evaluation, projection_uncurryModule]

/-- Hom同値のパラメータ加群に関する自然性。 -/
lemma curryModule_naturality {X Y F : Mod C M} (g : X ⟶ Y) (f : E ⊗ Y ⟶ F) :
    curryModule M E (E ◁ g ≫ f) = g ≫ curryModule M E f := by
  apply Mod.hom_ext
  apply evaluation_hom_ext M E F
  change E.X ◁ curryUnderlying M E (E ◁ g ≫ f) ≫ evaluation M E F =
    E.X ◁ (g.hom ≫ curryUnderlying M E f) ≫ evaluation M E F
  rw [curryUnderlying_evaluation, whiskerLeft_comp, Category.assoc,
    curryUnderlying_evaluation]
  change projection M E X ≫ map M (𝟙 E) g ≫ f.hom = _
  rw [projection_map_assoc]
  simp

/-- 内部Homの値域に関する関手。 -/
def internalHomFunctor : Mod C M ⥤ Mod C M :=
  Adjunction.rightAdjointOfEquiv (F := tensorLeft E) (tensorHomEquiv M E)
    (fun _ _ _ g f => curryModule_naturality M E g f)

/-- 釣り合いテンソル積と内部Homの随伴。 -/
def tensorInternalHomAdjunction : tensorLeft E ⊣ internalHomFunctor M E :=
  Adjunction.adjunctionOfEquivRight (F := tensorLeft E) (tensorHomEquiv M E)
    (fun _ _ _ g f => curryModule_naturality M E g f)

/-- 各加群は釣り合いテンソル積に関して閉対象である。 -/
instance moduleClosed : Closed E where
  rightAdj := internalHomFunctor M E
  adj := tensorInternalHomAdjunction M E

/-- 可換モノイド上の内部加群圏の閉モノイダル構造。 -/
instance moduleMonoidalClosed : MonoidalClosed (Mod C M) where
  closed E := moduleClosed M E

/-- 登録した内部Homの対象は等化子上の加群と一致する。 -/
lemma ihom_obj (F : Mod C M) : (ihom E).obj F = moduleObj M E F := rfl

/-- 登録した随伴のHom同値は構成した転置に一致する。 -/
lemma adjunction_homEquiv (X F : Mod C M) :
    (tensorInternalHomAdjunction M E).homEquiv X F = tensorHomEquiv M E X F := by
  apply Equiv.ext
  intro f
  simp only [tensorInternalHomAdjunction, Adjunction.adjunctionOfEquivRight,
    Adjunction.mkOfHomEquiv_homEquiv]

/-- 随伴の余単位は構成済みの加群としての評価。 -/
lemma adjunction_counit (F : Mod C M) :
    (tensorInternalHomAdjunction M E).counit.app F = evaluationModule M E F := by
  rw [← Adjunction.homEquiv_symm_id, adjunction_homEquiv]
  apply Mod.hom_ext
  change map M (𝟙 E) (𝟙 (moduleObj M E F)) ≫ (evaluationModule M E F).hom = _
  rw [map_id, Category.id_comp]

/-- 登録した閉構造の評価は構成済みの評価。 -/
lemma ihom_ev (F : Mod C M) : (ihom.ev E).app F = evaluationModule M E F :=
  adjunction_counit M E F

/-- 登録した閉構造のcurryingは構成済みの転置。 -/
lemma closed_curry {X F : Mod C M} (f : E ⊗ X ⟶ F) :
    curry f = curryModule M E f := by
  change (tensorInternalHomAdjunction M E).homEquiv X F f = _
  rw [adjunction_homEquiv]
  rfl

/-- Hom同値の値域に関する自然性。 -/
lemma curryModule_naturality_right {X F G : Mod C M} (f : E ⊗ X ⟶ F) (g : F ⟶ G) :
    curryModule M E (f ≫ g) = curryModule M E f ≫ (internalHomFunctor M E).map g := by
  rw [← closed_curry, ← closed_curry]
  exact curry_natural_right f g

end SerrePositivity.MonoidalModuleInternalHom
end

end ModuleClosed

/-! ## ModuleInternalHomFunctor（旧 SerrePositivity/CategoryTheory/Monoidal/ModuleInternalHomFunctor.lean） -/

/-! # 内部Homの二変数関手性と正則加群との比較 -/

@[expose] public section ModuleInternalHomFunctor
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalModuleInternalHom

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  [BraidedCategory C] (M : C) [MonObj M] [IsCommMonObj M] [HasEqualizers C]
  [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

/-- 原変数の加群射による内部Homの前合成。 -/
def preMap {E E' : Mod C M} (f : E' ⟶ E) (F : Mod C M) :
    moduleObj M E F ⟶ moduleObj M E' F := (pre f).app F

/-- 原変数では反変、値域では共変の内部Homの射。 -/
def homMap {E E' F F' : Mod C M} (f : E' ⟶ E) (g : F ⟶ F') :
    moduleObj M E F ⟶ moduleObj M E' F' :=
  preMap M f F ≫ (internalHomFunctor M E').map g

@[simp]
lemma preMap_id (E F : Mod C M) : preMap M (𝟙 E) F = 𝟙 (moduleObj M E F) := by
  simp [preMap, ihom_obj]

@[reassoc (attr := simp)]
lemma preMap_comp {E₁ E₂ E₃ : Mod C M} (f : E₁ ⟶ E₂) (g : E₂ ⟶ E₃) (F : Mod C M) :
    preMap M (f ≫ g) F = preMap M g F ≫ preMap M f F := by
  simp [preMap]

/-- 前合成と値域の射による後合成は交換する。 -/
@[reassoc]
lemma preMap_naturality {E E' F F' : Mod C M} (f : E' ⟶ E) (g : F ⟶ F') :
    preMap M f F ≫ (internalHomFunctor M E').map g =
      (internalHomFunctor M E).map g ≫ preMap M f F' :=
  pre_comm_ihom_map f g

/-- 前合成は評価と両立する。 -/
@[reassoc]
lemma preMap_evaluation {E E' : Mod C M} (f : E' ⟶ E) (F : Mod C M) :
    E' ◁ preMap M f F ≫ evaluationModule M E' F =
      f ▷ moduleObj M E F ≫ evaluationModule M E F := by
  simpa only [preMap, ihom_obj, ihom_ev] using id_tensor_pre_app_comp_ev f F

/-- 転置は原変数の前合成とも両立する。 -/
@[reassoc]
lemma curryModule_preMap {E E' X F : Mod C M} (f : E' ⟶ E) (g : E ⊗ X ⟶ F) :
    curryModule M E g ≫ preMap M f F = curryModule M E' (f ▷ X ≫ g) := by
  rw [← closed_curry, ← closed_curry]
  exact curry_pre_app f g

/-- 内部Homを原変数に反変な二変数関手として束ねる。 -/
def homBifunctor : (Mod C M)ᵒᵖ ⥤ Mod C M ⥤ Mod C M :=
  MonoidalClosed.internalHom

/-- 二変数関手の原変数の射は前合成。 -/
lemma homBifunctor_map {E E' : Mod C M} (f : E' ⟶ E) (F : Mod C M) :
    ((homBifunctor M).map f.op).app F = preMap M f F := rfl

/-- 正則加群からの内部Homの逆比較は左単位射の転置。 -/
def regularHomInv (F : Mod C M) : F ⟶ moduleObj M (Mod.regular M) F :=
  curryModule M (Mod.regular M) (λ_ F).hom

/-- 正則加群からの内部Homは単位を評価して元の加群へ戻る。 -/
def regularHomHom (F : Mod C M) : moduleObj M (Mod.regular M) F ⟶ F :=
  (λ_ (moduleObj M (Mod.regular M) F)).inv ≫ evaluationModule M (Mod.regular M) F

/-- 正則加群からの内部Homと元の加群の比較同型。 -/
def regularHomIso (F : Mod C M) : moduleObj M (Mod.regular M) F ≅ F where
  hom := regularHomHom M F
  inv := regularHomInv M F
  hom_inv_id := by
    apply uncurry_injective
    change uncurry (regularHomHom M F ≫ regularHomInv M F) = uncurry (𝟙 _)
    rw [regularHomInv, ← closed_curry, uncurry_natural_left, uncurry_curry]
    change (𝟙_ (Mod C M)) ◁ regularHomHom M F ≫ (λ_ F).hom = uncurry (𝟙 _)
    rw [leftUnitor_naturality, uncurry_id_eq_ev]
    simp only [regularHomHom, Iso.hom_inv_id_assoc, ← ihom_ev]
    rfl
  inv_hom_id := by
    unfold regularHomHom regularHomInv
    rw [← closed_curry]
    erw [leftUnitor_inv_naturality_assoc]
    rw [← ihom_ev]
    erw [whiskerLeft_curry_ihom_ev_app]
    exact Iso.inv_hom_id _

/-- 正則加群との内部Hom比較は値域に関して自然。 -/
@[reassoc]
lemma regularHomIso_naturality {F G : Mod C M} (f : F ⟶ G) :
    (internalHomFunctor M (Mod.regular M)).map f ≫ (regularHomIso M G).hom =
      (regularHomIso M F).hom ≫ f := by
  change (internalHomFunctor M (Mod.regular M)).map f ≫ regularHomHom M G =
    regularHomHom M F ≫ f
  unfold regularHomHom
  erw [leftUnitor_inv_naturality_assoc]
  rw [Category.assoc, ← ihom_ev, ← ihom_ev]
  erw [ihom.ev_naturality]
  rfl

/-- 正則加群からの内部Hom関手は恒等関手と自然同型。 -/
def regularHomNatIso : internalHomFunctor M (Mod.regular M) ≅ 𝟭 (Mod C M) :=
  NatIso.ofComponents (regularHomIso M) (fun f => regularHomIso_naturality M f)

end SerrePositivity.MonoidalModuleInternalHom
end

end ModuleInternalHomFunctor

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.4.3.13" (partial := special) "仮定：通常の対称閉モノイダル圏の可換内部モノイドと、内部 Hom と平衡テンソルを作る等化子・余等化子および保存条件（Lean が強い：通常の対称閉モノイダル圏と指定した等化子・余等化子）。結論：平衡テンソルは内部 Hom の左随伴なので通常圏の余極限を保存し、組紐によってもう一方の変数でも保存する（この仮定での HA の結論の一部に一致）。一般の幾何学的実現は含まれない。"] _root_.SerrePositivity.MonoidalModuleInternalHom.tensorInternalHomAdjunction
