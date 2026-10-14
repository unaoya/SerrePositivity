module

public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensor
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-! # 内部加群の右テンソルと可換係数の両側作用の整合性 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (M : C) [MonObj M]

/-- 第一因子の作用から得る、右にテンソルした対象の加群作用。 -/
@[instance_reducible] def tensorRightAction (E : Mod C M) (X : C) : ModObj M (E.X ⊗ X) where
  smul := (α_ M E.X X).inv ≫ γ[M,E.X] ▷ X
  one_smul := by
    change η[M] ▷ (E.X ⊗ X) ≫ (α_ M E.X X).inv ≫ γ[M,E.X] ▷ X =
      (λ_ (E.X ⊗ X)).hom
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, ModObj.one_smul_self]
    monoidal
  mul_smul := by
    change μ[M] ▷ (E.X ⊗ X) ≫ (α_ M E.X X).inv ≫ γ[M,E.X] ▷ X =
      (α_ M M (E.X ⊗ X)).hom ≫
        M ◁ ((α_ M E.X X).inv ≫ γ[M,E.X] ▷ X) ≫
          (α_ M E.X X).inv ≫ γ[M,E.X] ▷ X
    have he : μ[M] ▷ E.X ≫ γ[M,E.X] =
        (α_ M M E.X).hom ≫ M ◁ γ[M,E.X] ≫ γ[M,E.X] := ModObj.mul_smul_self M E.X
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, he]
    simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
    rw [associator_inv_naturality_middle_assoc]
    change (α_ (M ⊗ M) E.X X).inv ≫ (α_ M M E.X).hom ▷ X ≫
        (M ◁ γ[M,E.X]) ▷ X ≫ γ[M,E.X] ▷ X =
      (α_ M M (E.X ⊗ X)).hom ≫ M ◁ (α_ M E.X X).inv ≫
        (α_ M (M ⊗ E.X) X).inv ≫ (M ◁ γ[M,E.X]) ▷ X ≫ γ[M,E.X] ▷ X
    rw [pentagon_hom_inv_inv_inv_hom_assoc]

/-- 内部加群の右に対象Xをテンソルした内部加群。 -/
def tensorRightObj (E : Mod C M) (X : C) : Mod C M :=
  letI := tensorRightAction M E X
  ⟨E.X ⊗ X⟩

/-- 第一因子の加群の射と第二因子の射から得る、右テンソルの加群の射。 -/
def tensorRightMap {E E' : Mod C M} (f : E ⟶ E') {X Y : C} (g : X ⟶ Y) :
    tensorRightObj M E X ⟶ tensorRightObj M E' Y :=
  Mod.Hom.mk' (f.hom ⊗ₘ g) (by
    have hf : γ[M,E.X] ≫ f.hom = M ◁ f.hom ≫ γ[M,E'.X] := IsModHom.smul_hom
    change ((α_ M E.X X).inv ≫ γ[M,E.X] ▷ X) ≫ (f.hom ⊗ₘ g) =
      M ◁ (f.hom ⊗ₘ g) ≫ (α_ M E'.X Y).inv ≫ γ[M,E'.X] ▷ Y
    simp only [tensorHom_def, whiskerLeft_comp, Category.assoc]
    rw [← comp_whiskerRight_assoc, hf, comp_whiskerRight]
    rw [Category.assoc, ← whisker_exchange]
    rw [associator_inv_naturality_right_assoc, associator_inv_naturality_middle_assoc])

/-- 右テンソルの結合子は第一因子の加群作用と両立する。 -/
def tensorRightAssociator (E : Mod C M) (X Y : C) :
    tensorRightObj M (tensorRightObj M E X) Y ⟶ tensorRightObj M E (X ⊗ Y) :=
  Mod.Hom.mk' (α_ E.X X Y).hom (by
    change ((α_ M (E.X ⊗ X) Y).inv ≫
        ((α_ M E.X X).inv ≫ γ[M,E.X] ▷ X) ▷ Y) ≫ (α_ E.X X Y).hom =
      M ◁ (α_ E.X X Y).hom ≫ (α_ M E.X (X ⊗ Y)).inv ≫ γ[M,E.X] ▷ (X ⊗ Y)
    simp only [comp_whiskerRight, Category.assoc]
    rw [associator_naturality_left]
    change (α_ M (E.X ⊗ X) Y).inv ≫ (α_ M E.X X).inv ▷ Y ≫
        (α_ (M ⊗ E.X) X Y).hom ≫ γ[M,E.X] ▷ (X ⊗ Y) = _
    have h : (α_ M (E.X ⊗ X) Y).inv ≫ (α_ M E.X X).inv ▷ Y ≫
        (α_ (M ⊗ E.X) X Y).hom =
      M ◁ (α_ E.X X Y).hom ≫ (α_ M E.X (X ⊗ Y)).inv := by monoidal
    simpa only [Category.assoc] using
      congrArg (fun k => k ≫ γ[M,E.X] ▷ (X ⊗ Y)) h)

variable [BraidedCategory C] [IsCommMonObj M]

/-- 可換係数では左作用と右側へ移した作用が両立する。 -/
@[reassoc] lemma action_middle (E : Mod C M) :
    γ[M,E.X] ▷ M ≫ rightActionMap M E =
      (α_ M E.X M).hom ≫ M ◁ rightActionMap M E ≫ γ[M,E.X] := by
  simp only [rightActionMap, whiskerLeft_comp, Category.assoc]
  rw [BraidedCategory.braiding_naturality_left_assoc]
  have he : M ◁ γ[M,E.X] ≫ γ[M,E.X] =
      (α_ M M E.X).inv ≫ μ[M] ▷ E.X ≫ γ[M,E.X] :=
    ModObj.mul_smul_self_flip (M := M) E.X
  change (β_ (M ⊗ E.X) M).hom ≫ M ◁ γ[M,E.X] ≫ γ[M,E.X] = _
  nth_rw 1 [he]
  rw [BraidedCategory.braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, IsCommMonObj.mul_comm]
  rw [← he]

/-- 右側へ移した作用は可換係数の加群の射となる。 -/
def rightActionHom (E : Mod C M) : tensorRightObj M E M ⟶ E :=
  Mod.Hom.mk' (rightActionMap M E) (by
    change ((α_ M E.X M).inv ≫ γ[M,E.X] ▷ M) ≫ rightActionMap M E =
      M ◁ rightActionMap M E ≫ γ[M,E.X]
    rw [Category.assoc, action_middle, Iso.inv_hom_id_assoc])

end SerrePositivity.MonoidalBalancedTensor
