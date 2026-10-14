module

public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorModule
public import Mathlib.Tactic.CategoryTheory.Slice

/-! # 可換モノイド上の釣り合いテンソル積の左単位比較 -/

@[expose] public section

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
