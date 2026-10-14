module

public import SerrePositivity.CategoryTheory.Monoidal.ModuleInternalHomFreeNaturality

/-! # 自由原変数の内部Homの作用を同型で移した後の評価 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalModuleInternalHom

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  [BraidedCategory C] (M : C) [MonObj M] [IsCommMonObj M] [HasEqualizers C]
  (X : C) (F : Mod C M) {Y : C} (e : (ihom X).obj F.X ≅ Y)

/-- 通常の内部Homを同型で移した対象からの評価。 -/
def transportedEvaluation : X ⊗ Y ⟶ F.X := X ◁ e.inv ≫ (ihom.ev X).app F.X

/-- 同型で移した作用と評価の合成は、値域の作用から記述できる。 -/
@[reassoc]
lemma transportedAction_evaluation :
    X ◁ (M ◁ e.inv ≫ γ[M, (freeHomObj M X F).X] ≫ e.hom) ≫
        transportedEvaluation M X F e =
      (α_ X M Y).inv ≫ (β_ X M).hom ▷ Y ≫ (α_ M X Y).hom ≫
        M ◁ transportedEvaluation M X F e ≫ γ[M, F.X] := by
  unfold transportedEvaluation
  simp only [whiskerLeft_comp, Category.assoc]
  rw [← whiskerLeft_comp_assoc X e.hom e.inv, e.hom_inv_id, whiskerLeft_id, Category.id_comp]
  rw [freeHomObj_action_evaluation]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc]

/-- 通常の内部Homの作用を任意の同型で移送する。 -/
@[instance_reducible] def transportedAction : ModObj M Y := by
  letI := freeHomAction M X F
  have : IsMonHom (Iso.refl M).hom := inferInstanceAs (IsMonHom (𝟙 M))
  exact ModObj.ofIso (Iso.refl M) e

/-- 同型で移送した作用を持つ加群。 -/
def transportedObj : Mod C M :=
  letI := transportedAction M X F e
  ⟨Y⟩

/-- 作用の移送に伴う加群としての同型。 -/
def transportedIso : freeHomObj M X F ≅ transportedObj M X F e := by
  letI : ModObj M ((ihom X).obj F.X) := freeHomAction M X F
  letI : ModObj M Y := transportedAction M X F e
  have : IsModHom M e.hom := ⟨by
    change γ[M, (freeHomObj M X F).X] ≫ e.hom =
      M ◁ e.hom ≫ ((𝟙 M ⊗ₘ e.inv) ≫ γ[M, (freeHomObj M X F).X] ≫ e.hom)
    rw [id_tensorHom]
    simp only [← whiskerLeft_comp_assoc, e.hom_inv_id, whiskerLeft_id, Category.id_comp]⟩
  have : IsModHom M e.inv := inferInstance
  exact {
    hom := Mod.Hom.mk' e.hom IsModHom.smul_hom
    inv := Mod.Hom.mk' e.inv IsModHom.smul_hom
    hom_inv_id := Mod.hom_ext _ _ e.hom_inv_id
    inv_hom_id := Mod.hom_ext _ _ e.inv_hom_id }

/-- 移送した加群の実際の作用も、値域の作用と評価で記述できる。 -/
@[reassoc]
lemma transportedObj_action_evaluation :
    X ◁ γ[M, (transportedObj M X F e).X] ≫ transportedEvaluation M X F e =
      (α_ X M Y).inv ≫ (β_ X M).hom ▷ Y ≫ (α_ M X Y).hom ≫
        M ◁ transportedEvaluation M X F e ≫ γ[M, F.X] := by
  change X ◁ ((𝟙 M ⊗ₘ e.inv) ≫ γ[M, (freeHomObj M X F).X] ≫ e.hom) ≫ _ = _
  rw [id_tensorHom]
  exact transportedAction_evaluation M X F e

end SerrePositivity.MonoidalModuleInternalHom
