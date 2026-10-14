module

public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorModule
public import Mathlib.Tactic.CategoryTheory.Slice

/-! # 可換モノイド上の釣り合いテンソル積の右単位比較 -/

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
