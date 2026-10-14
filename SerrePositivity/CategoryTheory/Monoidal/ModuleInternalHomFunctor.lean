module

public import SerrePositivity.CategoryTheory.Monoidal.ModuleClosed

/-! # 内部Homの二変数関手性と正則加群との比較 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalModuleInternalHom

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  [BraidedCategory C] (M : C) [MonObj M] [IsCommMonObj M] [HasEqualizers C]
  [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

/-- 原変数の加群射による内部Homの前合成。 -/
def preMap {E E' : Mod C M} (f : E' ⟶ E) (F : Mod C M) :
    moduleObj M E F ⟶ moduleObj M E' F := (pre f).app F

/-- 原変数では反変、値域では共変の内部Homの射。 -/
def homMap {E E' F F' : Mod C M} (f : E' ⟶ E) (g : F ⟶ F') :
    moduleObj M E F ⟶ moduleObj M E' F' :=
  preMap M f F ≫ (internalHomFunctor M E').map g

@[simp]
lemma preMap_id (E F : Mod C M) : preMap M (𝟙 E) F = 𝟙 (moduleObj M E F) := by
  simp [preMap, ihom_obj]

@[reassoc (attr := simp)]
lemma preMap_comp {E₁ E₂ E₃ : Mod C M} (f : E₁ ⟶ E₂) (g : E₂ ⟶ E₃) (F : Mod C M) :
    preMap M (f ≫ g) F = preMap M g F ≫ preMap M f F := by
  simp [preMap]

/-- 前合成と値域の射による後合成は交換する。 -/
@[reassoc]
lemma preMap_naturality {E E' F F' : Mod C M} (f : E' ⟶ E) (g : F ⟶ F') :
    preMap M f F ≫ (internalHomFunctor M E').map g =
      (internalHomFunctor M E).map g ≫ preMap M f F' :=
  pre_comm_ihom_map f g

/-- 前合成は評価と両立する。 -/
@[reassoc]
lemma preMap_evaluation {E E' : Mod C M} (f : E' ⟶ E) (F : Mod C M) :
    E' ◁ preMap M f F ≫ evaluationModule M E' F =
      f ▷ moduleObj M E F ≫ evaluationModule M E F := by
  simpa only [preMap, ihom_obj, ihom_ev] using id_tensor_pre_app_comp_ev f F

/-- 転置は原変数の前合成とも両立する。 -/
@[reassoc]
lemma curryModule_preMap {E E' X F : Mod C M} (f : E' ⟶ E) (g : E ⊗ X ⟶ F) :
    curryModule M E g ≫ preMap M f F = curryModule M E' (f ▷ X ≫ g) := by
  rw [← closed_curry, ← closed_curry]
  exact curry_pre_app f g

/-- 内部Homを原変数に反変な二変数関手として束ねる。 -/
def homBifunctor : (Mod C M)ᵒᵖ ⥤ Mod C M ⥤ Mod C M :=
  MonoidalClosed.internalHom

/-- 二変数関手の原変数の射は前合成。 -/
lemma homBifunctor_map {E E' : Mod C M} (f : E' ⟶ E) (F : Mod C M) :
    ((homBifunctor M).map f.op).app F = preMap M f F := rfl

/-- 正則加群からの内部Homの逆比較は左単位射の転置。 -/
def regularHomInv (F : Mod C M) : F ⟶ moduleObj M (Mod.regular M) F :=
  curryModule M (Mod.regular M) (λ_ F).hom

/-- 正則加群からの内部Homは単位を評価して元の加群へ戻る。 -/
def regularHomHom (F : Mod C M) : moduleObj M (Mod.regular M) F ⟶ F :=
  (λ_ (moduleObj M (Mod.regular M) F)).inv ≫ evaluationModule M (Mod.regular M) F

/-- 正則加群からの内部Homと元の加群の比較同型。 -/
def regularHomIso (F : Mod C M) : moduleObj M (Mod.regular M) F ≅ F where
  hom := regularHomHom M F
  inv := regularHomInv M F
  hom_inv_id := by
    apply uncurry_injective
    change uncurry (regularHomHom M F ≫ regularHomInv M F) = uncurry (𝟙 _)
    rw [regularHomInv, ← closed_curry, uncurry_natural_left, uncurry_curry]
    change (𝟙_ (Mod C M)) ◁ regularHomHom M F ≫ (λ_ F).hom = uncurry (𝟙 _)
    rw [leftUnitor_naturality, uncurry_id_eq_ev]
    simp only [regularHomHom, Iso.hom_inv_id_assoc, ← ihom_ev]
    rfl
  inv_hom_id := by
    unfold regularHomHom regularHomInv
    rw [← closed_curry]
    erw [leftUnitor_inv_naturality_assoc]
    rw [← ihom_ev]
    erw [whiskerLeft_curry_ihom_ev_app]
    exact Iso.inv_hom_id _

/-- 正則加群との内部Hom比較は値域に関して自然。 -/
@[reassoc]
lemma regularHomIso_naturality {F G : Mod C M} (f : F ⟶ G) :
    (internalHomFunctor M (Mod.regular M)).map f ≫ (regularHomIso M G).hom =
      (regularHomIso M F).hom ≫ f := by
  change (internalHomFunctor M (Mod.regular M)).map f ≫ regularHomHom M G =
    regularHomHom M F ≫ f
  unfold regularHomHom
  erw [leftUnitor_inv_naturality_assoc]
  rw [Category.assoc, ← ihom_ev, ← ihom_ev]
  erw [ihom.ev_naturality]
  rfl

/-- 正則加群からの内部Hom関手は恒等関手と自然同型。 -/
def regularHomNatIso : internalHomFunctor M (Mod.regular M) ≅ 𝟭 (Mod C M) :=
  NatIso.ofComponents (regularHomIso M) (fun f => regularHomIso_naturality M f)

end SerrePositivity.MonoidalModuleInternalHom
