module

public import SerrePositivity.CategoryTheory.Monoidal.ModuleInternalHomAction
public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorFreePair

/-! # 自由加群からの内部Homの基礎対象

自由加群の生成元への制限により、内部Homの等化子を基礎圏の通常の内部Homへ比較する。
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
open MonoidalBalancedTensor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  (M : C) [MonObj M] [HasEqualizers C] (X : C) (F : Mod C M)

/-- 自由加群の右テンソルからの射を、積からの自由加群の射へ比較する。 -/
def freeTensorHomEquiv (Y : C) :
    (tensorRightObj M (MonoidalFreeModule.freeObj M X) Y ⟶ F) ≃
      (MonoidalFreeModule.freeObj M (X ⊗ Y) ⟶ F) where
  toFun f := (freeTensorIso M X Y).inv ≫ f
  invFun f := (freeTensorIso M X Y).hom ≫ f
  left_inv f := by simp
  right_inv f := by simp

/-- 自由原変数の内部Homへの射は、生成対象の通常の内部Homへの射と同値。 -/
def freeHomEquiv (Y : C) :
    (Y ⟶ obj M (MonoidalFreeModule.freeObj M X) F) ≃ (Y ⟶ (ihom X).obj F.X) :=
  (moduleHomEquiv M (MonoidalFreeModule.freeObj M X) F Y).trans
    ((freeTensorHomEquiv M X F Y).trans
      ((MonoidalFreeModule.freeHomEquiv M (X ⊗ Y) F).trans
        ((ihom.adjunction X).homEquiv Y F.X)))

/-- 比較のHom同値は生成元へ制限した評価の転置。 -/
lemma freeHomEquiv_apply {Y : C} (f : Y ⟶ obj M (MonoidalFreeModule.freeObj M X) F) :
    freeHomEquiv M X F Y f = curry (MonoidalFreeModule.generator M X ▷ Y ≫
      uncurry (f ≫ inclusion M (MonoidalFreeModule.freeObj M X) F)) := by
  change curry (MonoidalFreeModule.generator M (X ⊗ Y) ≫
    (α_ M X Y).inv ≫ uncurry (f ≫ inclusion M (MonoidalFreeModule.freeObj M X) F)) = _
  rw [← Category.assoc, generator_associator_inv]

/-- 自由原変数のHom同値はパラメータ対象に関して自然。 -/
lemma freeHomEquiv_naturality {Y Z : C} (g : Y ⟶ Z)
    (f : Z ⟶ obj M (MonoidalFreeModule.freeObj M X) F) :
    freeHomEquiv M X F Y (g ≫ f) = g ≫ freeHomEquiv M X F Z f := by
  rw [freeHomEquiv_apply, freeHomEquiv_apply, Category.assoc, uncurry_natural_left]
  rw [← whisker_exchange_assoc, curry_natural_left]

/-- 生成元上の評価を転置した順比較。 -/
def freeHomHom : obj M (MonoidalFreeModule.freeObj M X) F ⟶ (ihom X).obj F.X :=
  curry (MonoidalFreeModule.generator M X ▷ obj M (MonoidalFreeModule.freeObj M X) F ≫
    evaluation M (MonoidalFreeModule.freeObj M X) F)

/-- 通常の評価を自由加群へ延長して転置した逆比較。 -/
def freeHomInv : (ihom X).obj F.X ⟶ obj M (MonoidalFreeModule.freeObj M X) F :=
  moduleLift M (MonoidalFreeModule.freeObj M X) F
    ((freeTensorIso M X ((ihom X).obj F.X)).hom ≫
      MonoidalFreeModule.lift M (X ⊗ (ihom X).obj F.X) F ((ihom.ev X).app F.X))

lemma freeHomHom_eq : freeHomHom M X F = freeHomEquiv M X F _ (𝟙 _) := by
  rw [freeHomEquiv_apply, Category.id_comp]
  rfl

lemma freeHomInv_eq : freeHomInv M X F = (freeHomEquiv M X F _).symm (𝟙 _) := by
  change moduleLift M (MonoidalFreeModule.freeObj M X) F
    ((freeTensorIso M X ((ihom X).obj F.X)).hom ≫
      MonoidalFreeModule.lift M _ F ((ihom.ev X).app F.X)) =
    moduleLift M (MonoidalFreeModule.freeObj M X) F
      ((freeTensorIso M X ((ihom X).obj F.X)).hom ≫
        MonoidalFreeModule.lift M _ F (uncurry (𝟙 _)))
  rw [uncurry_id_eq_ev]

/-- 自由原変数の内部Homの基礎対象は生成対象からの通常の内部Homと同型。 -/
def freeHomIso : obj M (MonoidalFreeModule.freeObj M X) F ≅ (ihom X).obj F.X where
  hom := freeHomHom M X F
  inv := freeHomInv M X F
  hom_inv_id := by
    rw [freeHomHom_eq, freeHomInv_eq]
    apply (freeHomEquiv M X F _).injective
    rw [freeHomEquiv_naturality, Equiv.apply_symm_apply, Category.comp_id]
  inv_hom_id := by
    rw [freeHomHom_eq, freeHomInv_eq]
    have h := freeHomEquiv_naturality M X F
      ((freeHomEquiv M X F _).symm (𝟙 _)) (𝟙 _)
    simpa only [Category.comp_id, Equiv.apply_symm_apply] using h.symm

/-- 比較の順射は生成元への制限後の転置。 -/
lemma freeHomIso_hom : (freeHomIso M X F).hom =
    curry (MonoidalFreeModule.generator M X ▷ obj M (MonoidalFreeModule.freeObj M X) F ≫
      evaluation M (MonoidalFreeModule.freeObj M X) F) := rfl

/-- 比較の順射と評価の合成は生成元上の評価。 -/
@[reassoc]
lemma freeHomIso_evaluation : X ◁ (freeHomIso M X F).hom ≫ (ihom.ev X).app F.X =
    MonoidalFreeModule.generator M X ▷ obj M (MonoidalFreeModule.freeObj M X) F ≫
      evaluation M (MonoidalFreeModule.freeObj M X) F := by
  rw [freeHomIso_hom, whiskerLeft_curry_ihom_ev_app]

/-- 比較の逆射は通常の評価を自由加群へ延長した射の転置。 -/
lemma freeHomIso_inv : (freeHomIso M X F).inv =
    moduleLift M (MonoidalFreeModule.freeObj M X) F
      ((freeTensorIso M X ((ihom X).obj F.X)).hom ≫
        MonoidalFreeModule.lift M (X ⊗ (ihom X).obj F.X) F ((ihom.ev X).app F.X)) := rfl

/-- 逆比較と自由原変数の評価の合成公式。 -/
@[reassoc]
lemma freeHomIso_inv_evaluation :
    (MonoidalFreeModule.freeObj M X).X ◁ (freeHomIso M X F).inv ≫
      evaluation M (MonoidalFreeModule.freeObj M X) F =
    (α_ M X ((ihom X).obj F.X)).hom ≫ M ◁ (ihom.ev X).app F.X ≫ γ[M, F.X] := by
  rw [freeHomIso_inv]
  unfold moduleLift
  rw [lift_evaluation]
  rfl

variable [BraidedCategory C] [IsCommMonObj M]

/-- 自由原変数との比較で通常の内部Homへ移送した加群作用。 -/
@[instance_reducible] def freeHomAction : ModObj M ((ihom X).obj F.X) := by
  letI := internalHomAction M (MonoidalFreeModule.freeObj M X) F
  have : IsMonHom (Iso.refl M).hom := inferInstanceAs (IsMonHom (𝟙 M))
  exact ModObj.ofIso (Iso.refl M) (freeHomIso M X F)

/-- 通常の内部Homへ移送した作用を持つ加群。 -/
def freeHomObj : Mod C M :=
  letI := freeHomAction M X F
  ⟨(ihom X).obj F.X⟩

/-- 移送した作用の基礎対象上の具体式。 -/
lemma freeHomObj_action : γ[M, (freeHomObj M X F).X] =
    M ◁ (freeHomIso M X F).inv ≫ action M (MonoidalFreeModule.freeObj M X) F ≫
      (freeHomIso M X F).hom := by
  change (𝟙 M ⊗ₘ (freeHomIso M X F).inv) ≫
    action M (MonoidalFreeModule.freeObj M X) F ≫ (freeHomIso M X F).hom = _
  rw [id_tensorHom]

/-- 自由原変数の内部Homと通常の内部Homの加群としての比較。 -/
def freeHomModuleIso : moduleObj M (MonoidalFreeModule.freeObj M X) F ≅ freeHomObj M X F := by
  letI : ModObj M (obj M (MonoidalFreeModule.freeObj M X) F) :=
    internalHomAction M (MonoidalFreeModule.freeObj M X) F
  letI : ModObj M ((ihom X).obj F.X) := freeHomAction M X F
  have : IsModHom M (freeHomIso M X F).hom := ⟨by
    change action M (MonoidalFreeModule.freeObj M X) F ≫ (freeHomIso M X F).hom =
      M ◁ (freeHomIso M X F).hom ≫ ((𝟙 M ⊗ₘ (freeHomIso M X F).inv) ≫
        action M (MonoidalFreeModule.freeObj M X) F ≫ (freeHomIso M X F).hom)
    rw [id_tensorHom]
    simp only [← whiskerLeft_comp_assoc, Iso.hom_inv_id,
      whiskerLeft_id, Category.id_comp]⟩
  have : IsModHom M (freeHomIso M X F).inv := inferInstance
  exact {
    hom := Mod.Hom.mk' (freeHomIso M X F).hom IsModHom.smul_hom
    inv := Mod.Hom.mk' (freeHomIso M X F).inv IsModHom.smul_hom
    hom_inv_id := Mod.hom_ext _ _ (freeHomIso M X F).hom_inv_id
    inv_hom_id := Mod.hom_ext _ _ (freeHomIso M X F).inv_hom_id }

end SerrePositivity.MonoidalModuleInternalHom
