module

public import Mathlib.CategoryTheory.Monoidal.Mod

/-! # 基礎対象の同型による内部加群の作用の移送 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalModuleTransport

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (M : C) [MonObj M] (A : Mod C M) {Y : C} (e : A.X ≅ Y)

/-- 内部加群の作用を基礎対象の同型で移す。 -/
@[instance_reducible] def action : ModObj M Y := by
  have : IsMonHom (Iso.refl M).hom := inferInstanceAs (IsMonHom (𝟙 M))
  exact ModObj.ofIso (Iso.refl M) e

/-- 同型で作用を移した内部加群。 -/
def obj : Mod C M :=
  letI := action M A e
  ⟨Y⟩

/-- 作用の移送に伴う内部加群の全体の同型。 -/
def iso : A ≅ obj M A e := by
  letI : ModObj M Y := action M A e
  have : IsModHom M e.hom := ⟨by
    change γ[M, A.X] ≫ e.hom =
      M ◁ e.hom ≫ ((𝟙 M ⊗ₘ e.inv) ≫ γ[M, A.X] ≫ e.hom)
    rw [id_tensorHom]
    simp only [← whiskerLeft_comp_assoc, e.hom_inv_id, whiskerLeft_id, Category.id_comp]⟩
  have : IsModHom M e.inv := inferInstance
  exact {
    hom := Mod.Hom.mk' e.hom IsModHom.smul_hom
    inv := Mod.Hom.mk' e.inv IsModHom.smul_hom
    hom_inv_id := Mod.hom_ext _ _ e.hom_inv_id
    inv_hom_id := Mod.hom_ext _ _ e.inv_hom_id }

/-- 全体の比較の順射の基礎射は指定した同型の順射。 -/
lemma iso_hom : (iso M A e).hom.hom = e.hom := rfl

/-- 全体の比較の逆射の基礎射は指定した同型の逆射。 -/
lemma iso_inv : (iso M A e).inv.hom = e.inv := rfl

/-- 移送した加群の作用は比較の順逆を介した元の作用。 -/
lemma obj_action : γ[M, (obj M A e).X] = M ◁ e.inv ≫ γ[M, A.X] ≫ e.hom := by
  change (𝟙 M ⊗ₘ e.inv) ≫ γ[M, A.X] ≫ e.hom = _
  rw [id_tensorHom]

end SerrePositivity.MonoidalModuleTransport
