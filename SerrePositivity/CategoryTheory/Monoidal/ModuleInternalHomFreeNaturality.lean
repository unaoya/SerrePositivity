module

public import SerrePositivity.CategoryTheory.Monoidal.ModuleInternalHomFree
public import SerrePositivity.CategoryTheory.Monoidal.ModuleInternalHomFunctor
public import SerrePositivity.CategoryTheory.Monoidal.FreeModuleMonoidal

/-! # 自由原変数の内部Hom比較の自然性 -/

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
  [BraidedCategory C] (M : C) [MonObj M] [IsCommMonObj M] [HasEqualizers C]
  [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

/-- 前合成と評価の両立を基礎対象の射で記述する。 -/
@[reassoc]
lemma preMap_underlying_evaluation {E E' : Mod C M} (f : E' ⟶ E) (F : Mod C M) :
    E'.X ◁ (preMap M f F).hom ≫ evaluation M E' F =
      f.hom ▷ obj M E F ≫ evaluation M E F := by
  have h := congrArg (fun k => projection M E' (moduleObj M E F) ≫ k.hom)
    (preMap_evaluation M f F)
  change projection M E' (moduleObj M E F) ≫ map M (𝟙 E') (preMap M f F) ≫
      (evaluationModule M E' F).hom =
    projection M E' (moduleObj M E F) ≫ map M f (𝟙 (moduleObj M E F)) ≫
      (evaluationModule M E F).hom at h
  rw [projection_map_assoc, projection_map_assoc,
    projection_evaluationModule, projection_evaluationModule] at h
  simp only [Mod.id_hom', id_tensorHom, tensorHom_id] at h
  exact h

/-- 後合成と評価の両立を基礎対象の射で記述する。 -/
@[reassoc]
lemma map_underlying_evaluation (E : Mod C M) {F G : Mod C M} (f : F ⟶ G) :
    E.X ◁ ((internalHomFunctor M E).map f).hom ≫ evaluation M E G =
      evaluation M E F ≫ f.hom := by
  have h := ihom.ev_naturality (A := E) f
  rw [ihom_ev, ihom_ev] at h
  have h' := congrArg (fun k => projection M E (moduleObj M E F) ≫ k.hom) h
  change projection M E (moduleObj M E F) ≫
      map M (𝟙 E) ((internalHomFunctor M E).map f) ≫ (evaluationModule M E G).hom =
    projection M E (moduleObj M E F) ≫ (evaluationModule M E F).hom ≫ f.hom at h'
  erw [projection_map_assoc, projection_evaluationModule,
    projection_evaluationModule_assoc] at h'
  simp only [Mod.id_hom', id_tensorHom] at h'
  exact h'

/-- 自由原変数の比較は生成対象の射に関して反変自然。 -/
@[reassoc]
lemma freeHomIso_naturality_left {X Y : C} (f : X ⟶ Y) (F : Mod C M) :
    (preMap M (MonoidalFreeModule.freeMap M f) F).hom ≫ (freeHomIso M X F).hom =
      (freeHomIso M Y F).hom ≫ (pre f).app F.X := by
  apply uncurry_injective
  rw [freeHomIso_hom, freeHomIso_hom, uncurry_natural_left,
    uncurry_pre_app, uncurry_curry, uncurry_curry]
  erw [whisker_exchange_assoc, preMap_underlying_evaluation,
    ← comp_whiskerRight_assoc, generator_freeMap, comp_whiskerRight]
  simp only [Category.assoc]
  rfl

/-- 自由原変数の比較は値域の加群射に関して共変自然。 -/
@[reassoc]
lemma freeHomIso_naturality_right (X : C) {F G : Mod C M} (f : F ⟶ G) :
    ((internalHomFunctor M (MonoidalFreeModule.freeObj M X)).map f).hom ≫
        (freeHomIso M X G).hom =
      (freeHomIso M X F).hom ≫ (ihom X).map f.hom := by
  apply uncurry_injective
  rw [freeHomIso_hom, freeHomIso_hom, uncurry_natural_left,
    uncurry_natural_right, uncurry_curry, uncurry_curry]
  erw [whisker_exchange_assoc, map_underlying_evaluation]
  simp only [Category.assoc]
  rfl

omit [MonoidalClosed C] [IsCommMonObj M] [HasEqualizers C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 生成元に右から係数を作用させると、通常の交換射になる。 -/
@[reassoc]
lemma generator_rightAction (X : C) :
    MonoidalFreeModule.generator M X ▷ M ≫
      rightActionMap M (MonoidalFreeModule.freeObj M X) = (β_ X M).hom := by
  rw [rightActionMap, BraidedCategory.braiding_naturality_left_assoc,
    MonoidalFreeModule.generator_action, Category.comp_id]

omit [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 通常の内部Homに移送した作用を、値域の作用と評価で記述する。 -/
@[reassoc]
lemma freeHomObj_action_evaluation (X : C) (F : Mod C M) :
    X ◁ γ[M, (freeHomObj M X F).X] ≫ (ihom.ev X).app F.X =
      (α_ X M ((ihom X).obj F.X)).inv ≫ (β_ X M).hom ▷ (ihom X).obj F.X ≫
        (α_ M X ((ihom X).obj F.X)).hom ≫ M ◁ (ihom.ev X).app F.X ≫ γ[M, F.X] := by
  rw [freeHomObj_action]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [freeHomIso_evaluation]
  erw [whisker_exchange_assoc, action_evaluation]
  erw [whisker_exchange_assoc, associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    freeHomIso_inv_evaluation, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc, generator_rightAction]
  rfl

omit [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 移送した作用は、係数を交換して値域に作用させる評価の転置。 -/
lemma freeHomObj_action_formula (X : C) (F : Mod C M) :
    γ[M, (freeHomObj M X F).X] =
      curry ((α_ X M ((ihom X).obj F.X)).inv ≫ (β_ X M).hom ▷ (ihom X).obj F.X ≫
        (α_ M X ((ihom X).obj F.X)).hom ≫ M ◁ (ihom.ev X).app F.X ≫ γ[M, F.X]) := by
  apply uncurry_injective
  rw [uncurry_curry, uncurry_eq]
  exact freeHomObj_action_evaluation M X F

/-- 通常の内部Homへ移送した作用を持つ加群の二変数の射。 -/
def freeHomMap {X Y : C} (f : X ⟶ Y) {F G : Mod C M} (g : F ⟶ G) :
    freeHomObj M Y F ⟶ freeHomObj M X G :=
  (freeHomModuleIso M Y F).inv ≫ homMap M (MonoidalFreeModule.freeMap M f) g ≫
    (freeHomModuleIso M X G).hom

/-- 移送した加群の射の基礎射は通常の内部Homの前合成と後合成。 -/
lemma freeHomMap_hom {X Y : C} (f : X ⟶ Y) {F G : Mod C M} (g : F ⟶ G) :
    (freeHomMap M f g).hom = (pre f).app F.X ≫ (ihom X).map g.hom := by
  dsimp only [freeHomMap, homMap]
  simp only [Mod.comp_hom', Category.assoc]
  erw [freeHomIso_naturality_right, freeHomIso_naturality_left_assoc,
    Iso.inv_hom_id_assoc]

/-- 自由原変数の加群としての比較は両変数の射に関して自然。 -/
@[reassoc]
lemma freeHomModuleIso_naturality {X Y : C} (f : X ⟶ Y) {F G : Mod C M} (g : F ⟶ G) :
    homMap M (MonoidalFreeModule.freeMap M f) g ≫ (freeHomModuleIso M X G).hom =
      (freeHomModuleIso M Y F).hom ≫ freeHomMap M f g := by
  unfold freeHomMap
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end SerrePositivity.MonoidalModuleInternalHom
