module

public import SerrePositivity.CategoryTheory.Monoidal.ModuleInternalHom
public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorRightUnit

/-! # 可換係数上の内部Homの加群作用 -/

@[expose] public section

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
