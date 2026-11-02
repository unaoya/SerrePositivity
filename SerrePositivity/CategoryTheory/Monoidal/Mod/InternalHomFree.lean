module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.InternalHom
public import SerrePositivity.CategoryTheory.Monoidal.Mod.FreeTensor

/-!
# Monoidal.Mod.InternalHomFree

## 概要
関連する圏論の構成と補題をまとめる。各構成の詳細は以下の元モジュールの説明を参照。

## 方針
元の宣言と証明を保持し、依存順に section を分けて配置する。

## 規約
公開宣言名・名前空間・宇宙変数の意味を変更しない。元の module docstring は各節に保存する。

## 使われ方
旧モジュールの利用元は `SerrePositivity.CategoryTheory.Monoidal.Mod.InternalHomFree` を直接 import する。
-/

/-! ## ModuleInternalHomFree（旧 SerrePositivity/CategoryTheory/Monoidal/ModuleInternalHomFree.lean） -/

/-! # 自由加群からの内部Homの基礎対象

自由加群の生成元への制限により、内部Homの等化子を基礎圏の通常の内部Homへ比較する。
-/

@[expose] public section ModuleInternalHomFree
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
end

end ModuleInternalHomFree

/-! ## ModuleInternalHomFreeNaturality（旧 SerrePositivity/CategoryTheory/Monoidal/ModuleInternalHomFreeNaturality.lean） -/

/-! # 自由原変数の内部Hom比較の自然性 -/

@[expose] public section ModuleInternalHomFreeNaturality
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
end

end ModuleInternalHomFreeNaturality

/-! ## ModuleInternalHomFreeLeftEvaluation（旧 SerrePositivity/CategoryTheory/Monoidal/ModuleInternalHomFreeLeftEvaluation.lean） -/

/-! # 左自由因子との比較の下での逆転置と通常の評価 -/

@[expose] public section ModuleInternalHomFreeLeftEvaluation
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalModuleInternalHom

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  [SymmetricCategory C] (M : C) [MonObj M] [IsCommMonObj M]
  [HasEqualizers C] [HasCoequalizers C]
  [∀ Z : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]

/-- 左自由因子の比較の逆射と逆転置の合成は、比較した通常の内部Homの評価。 -/
lemma freeLeftIso_uncurry (X : C) {A F : Mod C M}
    (f : A ⟶ moduleObj M (MonoidalFreeModule.freeObj M X) F) :
    (MonoidalBalancedTensor.freeLeftIso M X A).inv.hom ≫
        (uncurryModule M (MonoidalFreeModule.freeObj M X) f).hom =
      X ◁ (f.hom ≫ (freeHomIso M X F).hom) ≫ (ihom.ev X).app F.X := by
  rw [MonoidalBalancedTensor.freeLeftIso_inv]
  rw [Category.assoc, projection_uncurryModule]
  rw [← whisker_exchange_assoc]
  erw [← freeHomIso_evaluation]
  rw [← whiskerLeft_comp_assoc]

end SerrePositivity.MonoidalModuleInternalHom
end

end ModuleInternalHomFreeLeftEvaluation

/-! ## ModuleInternalHomTransport（旧 SerrePositivity/CategoryTheory/Monoidal/ModuleInternalHomTransport.lean） -/

/-! # 自由原変数の内部Homの作用を同型で移した後の評価 -/

@[expose] public section ModuleInternalHomTransport
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
end

end ModuleInternalHomTransport

/-! ## ModuleInternalHomTransportComparison（旧 SerrePositivity/CategoryTheory/Monoidal/ModuleInternalHomTransportComparison.lean） -/

/-! # 内部Homの作用の移送を二つの比較同型で計算する -/

@[expose] public section ModuleInternalHomTransportComparison
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalModuleInternalHom

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  [BraidedCategory C] (M : C) [MonObj M] [IsCommMonObj M] [HasEqualizers C]
  (X : C) (F : Mod C M) {Y Z : C} (e : (ihom X).obj F.X ≅ Y) (d : Y ≅ Z)

/-- 比較の合成による移送を、最初の移送済み加群との同型として表示する。 -/
def furtherTransportedIso : transportedObj M X F e ≅ transportedObj M X F (e ≪≫ d) :=
  (transportedIso M X F e).symm ≪≫ transportedIso M X F (e ≪≫ d)

/-- 二段目の加群比較の基礎射は二段目の比較の順射。 -/
lemma furtherTransportedIso_hom :
    (furtherTransportedIso M X F e d).hom.hom = d.hom := by
  change e.inv ≫ (e.hom ≫ d.hom) = d.hom
  simp only [Iso.inv_hom_id_assoc]

/-- 二段目の加群比較の逆基礎射は二段目の比較の逆射。 -/
lemma furtherTransportedIso_inv :
    (furtherTransportedIso M X F e d).inv.hom = d.inv := by
  change (d.inv ≫ e.inv) ≫ e.hom = d.inv
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.MonoidalModuleInternalHom
end

end ModuleInternalHomTransportComparison
