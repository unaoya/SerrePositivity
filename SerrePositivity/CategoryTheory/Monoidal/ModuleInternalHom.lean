module

public import SerrePositivity.CategoryTheory.Monoidal.TensorRightModule
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! # 内部加群の内部Homの基礎対象

作用との両立を表す二つの射の等化子と、パラメータ付き線形射の普遍性を構成する。
この段階では等化子上の加群作用は構成しない。
-/

@[expose] public section

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
