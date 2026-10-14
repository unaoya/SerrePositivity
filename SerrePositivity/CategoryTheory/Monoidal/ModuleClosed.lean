module

public import SerrePositivity.CategoryTheory.Monoidal.ModuleInternalHomAction
public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorMonoidal

/-! # 可換モノイド上の加群圏の閉構造

釣り合いテンソル積からの加群射と内部Homへの加群射を自然なHom同値で比較する。
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
  [BraidedCategory C] (M : C) [MonObj M] [IsCommMonObj M] [HasEqualizers C]
  [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]
  (E : Mod C M)

/-- 商からの加群射の基礎対象上の転置。 -/
def curryUnderlying {X F : Mod C M} (f : E ⊗ X ⟶ F) : X.X ⟶ obj M E F :=
  moduleLift M E F (projectionModuleHom M E X ≫ f)

/-- 基礎対象上の転置と評価の合成公式。 -/
@[reassoc (attr := simp)]
lemma curryUnderlying_evaluation {X F : Mod C M} (f : E ⊗ X ⟶ F) :
    E.X ◁ curryUnderlying M E f ≫ evaluation M E F = projection M E X ≫ f.hom := by
  unfold curryUnderlying moduleLift
  rw [lift_evaluation]
  rfl

/-- 釣り合い条件から転置の加群作用との両立が従う。 -/
def curryModule {X F : Mod C M} (f : E ⊗ X ⟶ F) : X ⟶ moduleObj M E F :=
  Mod.Hom.mk' (curryUnderlying M E f) (by
    change γ[M, X.X] ≫ curryUnderlying M E f = M ◁ curryUnderlying M E f ≫ action M E F
    apply evaluation_hom_ext M E F
    simp only [whiskerLeft_comp, Category.assoc]
    rw [curryUnderlying_evaluation, action_evaluation,
      associator_inv_naturality_right_assoc, whisker_exchange_assoc,
      curryUnderlying_evaluation]
    have h := projection_condition M E X
    change rightActionMap M E ▷ X.X ≫ projection M E X =
      ((α_ E.X M X.X).hom ≫ E.X ◁ γ[M, X.X]) ≫ projection M E X at h
    simp only [Category.assoc] at h
    rw [reassoc_of% h, Iso.inv_hom_id_assoc])

/-- 内部Homへの加群射をテンソル積からの加群射へ戻す。 -/
def uncurryModule {X F : Mod C M} (f : X ⟶ moduleObj M E F) : E ⊗ X ⟶ F :=
  moduleMap M (𝟙 E) f ≫ evaluationModule M E F

/-- 逆転置の商の標準射上での公式。 -/
@[reassoc (attr := simp)]
lemma projection_uncurryModule {X F : Mod C M} (f : X ⟶ moduleObj M E F) :
    projection M E X ≫ (uncurryModule M E f).hom = E.X ◁ f.hom ≫ evaluation M E F := by
  change projection M E X ≫ map M (𝟙 E) f ≫ (evaluationModule M E F).hom = _
  rw [projection_map_assoc, projection_evaluationModule]
  simp

/-- テンソル積からの加群射と内部Homへの加群射の全単射。 -/
def tensorHomEquiv (X F : Mod C M) : (E ⊗ X ⟶ F) ≃ (X ⟶ moduleObj M E F) where
  toFun := curryModule M E
  invFun := uncurryModule M E
  left_inv f := by
    apply Mod.hom_ext
    apply (cancel_epi (projection M E X)).mp
    rw [projection_uncurryModule]
    exact curryUnderlying_evaluation M E f
  right_inv f := by
    apply Mod.hom_ext
    apply evaluation_hom_ext M E F
    change E.X ◁ curryUnderlying M E (uncurryModule M E f) ≫ evaluation M E F = _
    rw [curryUnderlying_evaluation, projection_uncurryModule]

/-- Hom同値のパラメータ加群に関する自然性。 -/
lemma curryModule_naturality {X Y F : Mod C M} (g : X ⟶ Y) (f : E ⊗ Y ⟶ F) :
    curryModule M E (E ◁ g ≫ f) = g ≫ curryModule M E f := by
  apply Mod.hom_ext
  apply evaluation_hom_ext M E F
  change E.X ◁ curryUnderlying M E (E ◁ g ≫ f) ≫ evaluation M E F =
    E.X ◁ (g.hom ≫ curryUnderlying M E f) ≫ evaluation M E F
  rw [curryUnderlying_evaluation, whiskerLeft_comp, Category.assoc,
    curryUnderlying_evaluation]
  change projection M E X ≫ map M (𝟙 E) g ≫ f.hom = _
  rw [projection_map_assoc]
  simp

/-- 内部Homの値域に関する関手。 -/
def internalHomFunctor : Mod C M ⥤ Mod C M :=
  Adjunction.rightAdjointOfEquiv (F := tensorLeft E) (tensorHomEquiv M E)
    (fun _ _ _ g f => curryModule_naturality M E g f)

/-- 釣り合いテンソル積と内部Homの随伴。 -/
def tensorInternalHomAdjunction : tensorLeft E ⊣ internalHomFunctor M E :=
  Adjunction.adjunctionOfEquivRight (F := tensorLeft E) (tensorHomEquiv M E)
    (fun _ _ _ g f => curryModule_naturality M E g f)

/-- 各加群は釣り合いテンソル積に関して閉対象である。 -/
instance moduleClosed : Closed E where
  rightAdj := internalHomFunctor M E
  adj := tensorInternalHomAdjunction M E

/-- 可換モノイド上の内部加群圏の閉モノイダル構造。 -/
instance moduleMonoidalClosed : MonoidalClosed (Mod C M) where
  closed E := moduleClosed M E

/-- 登録した内部Homの対象は等化子上の加群と一致する。 -/
lemma ihom_obj (F : Mod C M) : (ihom E).obj F = moduleObj M E F := rfl

/-- 登録した随伴のHom同値は構成した転置に一致する。 -/
lemma adjunction_homEquiv (X F : Mod C M) :
    (tensorInternalHomAdjunction M E).homEquiv X F = tensorHomEquiv M E X F := by
  apply Equiv.ext
  intro f
  simp only [tensorInternalHomAdjunction, Adjunction.adjunctionOfEquivRight,
    Adjunction.mkOfHomEquiv_homEquiv]

/-- 随伴の余単位は構成済みの加群としての評価。 -/
lemma adjunction_counit (F : Mod C M) :
    (tensorInternalHomAdjunction M E).counit.app F = evaluationModule M E F := by
  rw [← Adjunction.homEquiv_symm_id, adjunction_homEquiv]
  apply Mod.hom_ext
  change map M (𝟙 E) (𝟙 (moduleObj M E F)) ≫ (evaluationModule M E F).hom = _
  rw [map_id, Category.id_comp]

/-- 登録した閉構造の評価は構成済みの評価。 -/
lemma ihom_ev (F : Mod C M) : (ihom.ev E).app F = evaluationModule M E F :=
  adjunction_counit M E F

/-- 登録した閉構造のcurryingは構成済みの転置。 -/
lemma closed_curry {X F : Mod C M} (f : E ⊗ X ⟶ F) :
    curry f = curryModule M E f := by
  change (tensorInternalHomAdjunction M E).homEquiv X F f = _
  rw [adjunction_homEquiv]
  rfl

/-- Hom同値の値域に関する自然性。 -/
lemma curryModule_naturality_right {X F G : Mod C M} (f : E ⊗ X ⟶ F) (g : F ⟶ G) :
    curryModule M E (f ≫ g) = curryModule M E f ≫ (internalHomFunctor M E).map g := by
  rw [← closed_curry, ← closed_curry]
  exact curry_natural_right f g

end SerrePositivity.MonoidalModuleInternalHom
