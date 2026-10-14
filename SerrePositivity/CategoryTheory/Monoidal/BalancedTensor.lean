module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! # 内部加群の釣り合いテンソル積の基礎対象

二つの作用を同一視する余等化子と、釣り合い条件を満たす射の普遍性を構成する。
商の構成はテンソル積の余極限保存を仮定しない。商上の加群作用の登録は別に行う。
-/

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

/-- 左作用をbraidingで右側へ移した射。 -/
def rightActionMap (E : Mod C M) : E.X ⊗ M ⟶ E.X :=
  (β_ E.X M).hom ≫ γ[M, E.X]

/-- 右側へ移した作用の射は加群の射に関して自然。 -/
@[reassoc] lemma rightActionMap_naturality {E E' : Mod C M} (f : E ⟶ E') :
    rightActionMap M E ≫ f.hom = f.hom ▷ M ≫ rightActionMap M E' := by
  have hf : γ[M, E.X] ≫ f.hom = M ◁ f.hom ≫ γ[M, E'.X] := IsModHom.smul_hom
  rw [rightActionMap, Category.assoc, hf,
    ← BraidedCategory.braiding_naturality_left_assoc]
  rfl

/-- 第一の加群の右側へ移した作用を使う、釣り合い関係式の左辺。 -/
def relationLeft (E F : Mod C M) : (E.X ⊗ M) ⊗ F.X ⟶ E.X ⊗ F.X :=
  rightActionMap M E ▷ F.X

/-- 第二の加群の左作用を使う、釣り合い関係式の右辺。 -/
def relationRight (E F : Mod C M) : (E.X ⊗ M) ⊗ F.X ⟶ E.X ⊗ F.X :=
  (α_ E.X M F.X).hom ≫ E.X ◁ γ[M, F.X]

variable [HasCoequalizers C]

/-- 二つの作用を同一視した釣り合いテンソル積の基礎対象。 -/
def obj (E F : Mod C M) : C := coequalizer (relationLeft M E F) (relationRight M E F)

/-- 二つの加群の通常のテンソル積から、釣り合い商への標準射。 -/
def projection (E F : Mod C M) : E.X ⊗ F.X ⟶ obj M E F :=
  coequalizer.π (relationLeft M E F) (relationRight M E F)

instance projection_epi (E F : Mod C M) : Epi (projection M E F) :=
  inferInstanceAs (Epi (coequalizer.π (relationLeft M E F) (relationRight M E F)))

/-- 標準射は二つの加群作用を同一視する。 -/
@[reassoc] lemma projection_condition (E F : Mod C M) :
    relationLeft M E F ≫ projection M E F = relationRight M E F ≫ projection M E F :=
  coequalizer.condition _ _

/-- 二つの加群作用に関する釣り合い条件を満たす射。 -/
def BalancedMap (E F : Mod C M) (Y : C) :=
  { f : E.X ⊗ F.X ⟶ Y // relationLeft M E F ≫ f = relationRight M E F ≫ f }

/-- 釣り合い条件を満たす射を商全体へ降ろす。 -/
def desc {E F : Mod C M} {Y : C} (f : BalancedMap M E F Y) : obj M E F ⟶ Y :=
  coequalizer.desc f.val f.property

/-- 降下した射は標準射上で指定された値に一致する。 -/
@[reassoc (attr := simp)] lemma projection_desc {E F : Mod C M} {Y : C}
    (f : BalancedMap M E F Y) : projection M E F ≫ desc M f = f.val :=
  coequalizer.π_desc _ _

/-- 釣り合い商からの射は標準射との合成で決まる。 -/
lemma hom_ext {E F : Mod C M} {Y : C} (f g : obj M E F ⟶ Y)
    (h : projection M E F ≫ f = projection M E F ≫ g) : f = g :=
  coequalizer.hom_ext h

/-- 指定された釣り合い射の降下は一意。 -/
lemma desc_unique {E F : Mod C M} {Y : C} (f : BalancedMap M E F Y)
    (g : obj M E F ⟶ Y) (h : projection M E F ≫ g = f.val) : g = desc M f := by
  apply hom_ext M
  rw [projection_desc]
  exact h

/-- 釣り合い商からの射と、釣り合い条件を満たす射との同値。 -/
def homEquiv (E F : Mod C M) (Y : C) : (obj M E F ⟶ Y) ≃ BalancedMap M E F Y where
  toFun f := ⟨projection M E F ≫ f, by
    rw [← Category.assoc, ← Category.assoc, projection_condition]⟩
  invFun := desc M
  left_inv f := (desc_unique M _ f rfl).symm
  right_inv f := Subtype.ext (projection_desc M f)

omit [HasCoequalizers C] in
/-- 第一の作用を使う関係式は二つの加群の射に関して自然。 -/
@[reassoc] lemma relationLeft_naturality {E E' F F' : Mod C M} (f : E ⟶ E') (g : F ⟶ F') :
    ((f.hom ⊗ₘ 𝟙 M) ⊗ₘ g.hom) ≫ relationLeft M E' F' =
      relationLeft M E F ≫ (f.hom ⊗ₘ g.hom) := by
  rw [relationLeft, relationLeft, ← tensorHom_id, ← tensorHom_id]
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  simp only [Category.comp_id, Category.id_comp, tensorHom_id, ← rightActionMap_naturality]

omit [HasCoequalizers C] [BraidedCategory C] in
/-- 第二の作用を使う関係式は二つの加群の射に関して自然。 -/
@[reassoc] lemma relationRight_naturality {E E' F F' : Mod C M} (f : E ⟶ E') (g : F ⟶ F') :
    ((f.hom ⊗ₘ 𝟙 M) ⊗ₘ g.hom) ≫ relationRight M E' F' =
      relationRight M E F ≫ (f.hom ⊗ₘ g.hom) := by
  rw [relationRight, associator_naturality_assoc, relationRight, Category.assoc]
  congr 1
  rw [← id_tensorHom, tensorHom_comp_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom]
  have hg : γ[M, F.X] ≫ g.hom = M ◁ g.hom ≫ γ[M, F'.X] := IsModHom.smul_hom
  simp only [Category.comp_id, Category.id_comp, id_tensorHom]
  rw [hg]

/-- 二つの加群の射を、釣り合い商の射へ降ろす。 -/
def map {E E' F F' : Mod C M} (f : E ⟶ E') (g : F ⟶ F') : obj M E F ⟶ obj M E' F' :=
  desc M ⟨(f.hom ⊗ₘ g.hom) ≫ projection M E' F', by
    rw [← Category.assoc, ← relationLeft_naturality, Category.assoc,
      projection_condition, ← Category.assoc, relationRight_naturality, Category.assoc]⟩

/-- 商へ誘導した射は標準射と両立する。 -/
@[reassoc (attr := simp)] lemma projection_map {E E' F F' : Mod C M}
    (f : E ⟶ E') (g : F ⟶ F') :
    projection M E F ≫ map M f g = (f.hom ⊗ₘ g.hom) ≫ projection M E' F' :=
  projection_desc M _

/-- 二つの恒等射は商上の恒等射へ送られる。 -/
@[simp] lemma map_id (E F : Mod C M) : map M (𝟙 E) (𝟙 F) = 𝟙 (obj M E F) := by
  apply hom_ext M
  rw [projection_map]
  change (𝟙 E.X ⊗ₘ 𝟙 F.X) ≫ projection M E F = projection M E F ≫ 𝟙 _
  simp

/-- 二つの加群の射の合成は商上の射の合成へ送られる。 -/
lemma map_comp {E₁ E₂ E₃ F₁ F₂ F₃ : Mod C M}
    (f₁ : E₁ ⟶ E₂) (f₂ : E₂ ⟶ E₃) (g₁ : F₁ ⟶ F₂) (g₂ : F₂ ⟶ F₃) :
    map M (f₁ ≫ f₂) (g₁ ≫ g₂) = map M f₁ g₁ ≫ map M f₂ g₂ := by
  apply hom_ext M
  rw [projection_map, projection_map_assoc, projection_map]
  change ((f₁.hom ≫ f₂.hom) ⊗ₘ (g₁.hom ≫ g₂.hom)) ≫ projection M E₃ F₃ =
    (f₁.hom ⊗ₘ g₁.hom) ≫ (f₂.hom ⊗ₘ g₂.hom) ≫ projection M E₃ F₃
  rw [← tensorHom_comp_tensorHom, Category.assoc]

/-- 二つの加群から釣り合いテンソル積の基礎対象を作る二変数関手。 -/
def bifunctor : Mod C M × Mod C M ⥤ C where
  obj EF := obj M EF.1 EF.2
  map fg := map M fg.1 fg.2
  map_id EF := map_id M EF.1 EF.2
  map_comp fg gh := map_comp M fg.1 gh.1 fg.2 gh.2

end SerrePositivity.MonoidalBalancedTensor
