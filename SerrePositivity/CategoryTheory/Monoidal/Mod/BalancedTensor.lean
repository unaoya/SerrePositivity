module


public meta import SerrePositivity.Util.Citation
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
public import SerrePositivity.CategoryTheory.Monoidal.Mod.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.Tactic.CategoryTheory.Slice

/-!
# Monoidal.Mod.BalancedTensor

## 概要
関連する圏論の構成と補題をまとめる。各構成の詳細は以下の元モジュールの説明を参照。

## 方針
元の宣言と証明を保持し、依存順に section を分けて配置する。

## 規約
公開宣言名・名前空間・宇宙変数の意味を変更しない。元の module docstring は各節に保存する。

## 使われ方
旧モジュールの利用元は `SerrePositivity.CategoryTheory.Monoidal.Mod.BalancedTensor` を直接 import する。
-/

/-! ## BalancedTensor（旧 SerrePositivity/CategoryTheory/Monoidal/BalancedTensor.lean） -/

/-! # 内部加群の釣り合いテンソル積の基礎対象

二つの作用を同一視する余等化子と、釣り合い条件を満たす射の普遍性を構成する。
商の構成はテンソル積の余極限保存を仮定しない。商上の加群作用の登録は別に行う。
-/

@[expose] public section BalancedTensor
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
end

end BalancedTensor

/-! ## TensorRightModule（旧 SerrePositivity/CategoryTheory/Monoidal/TensorRightModule.lean） -/

/-! # 内部加群の右テンソルと可換係数の両側作用の整合性 -/

@[expose] public section TensorRightModule
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (M : C) [MonObj M]

/-- 第一因子の作用から得る、右にテンソルした対象の加群作用。 -/
@[instance_reducible] def tensorRightAction (E : Mod C M) (X : C) : ModObj M (E.X ⊗ X) where
  smul := (α_ M E.X X).inv ≫ γ[M,E.X] ▷ X
  one_smul := by
    change η[M] ▷ (E.X ⊗ X) ≫ (α_ M E.X X).inv ≫ γ[M,E.X] ▷ X =
      (λ_ (E.X ⊗ X)).hom
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, ModObj.one_smul_self]
    monoidal
  mul_smul := by
    change μ[M] ▷ (E.X ⊗ X) ≫ (α_ M E.X X).inv ≫ γ[M,E.X] ▷ X =
      (α_ M M (E.X ⊗ X)).hom ≫
        M ◁ ((α_ M E.X X).inv ≫ γ[M,E.X] ▷ X) ≫
          (α_ M E.X X).inv ≫ γ[M,E.X] ▷ X
    have he : μ[M] ▷ E.X ≫ γ[M,E.X] =
        (α_ M M E.X).hom ≫ M ◁ γ[M,E.X] ≫ γ[M,E.X] := ModObj.mul_smul_self M E.X
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, he]
    simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
    rw [associator_inv_naturality_middle_assoc]
    change (α_ (M ⊗ M) E.X X).inv ≫ (α_ M M E.X).hom ▷ X ≫
        (M ◁ γ[M,E.X]) ▷ X ≫ γ[M,E.X] ▷ X =
      (α_ M M (E.X ⊗ X)).hom ≫ M ◁ (α_ M E.X X).inv ≫
        (α_ M (M ⊗ E.X) X).inv ≫ (M ◁ γ[M,E.X]) ▷ X ≫ γ[M,E.X] ▷ X
    rw [pentagon_hom_inv_inv_inv_hom_assoc]

/-- 内部加群の右に対象Xをテンソルした内部加群。 -/
def tensorRightObj (E : Mod C M) (X : C) : Mod C M :=
  letI := tensorRightAction M E X
  ⟨E.X ⊗ X⟩

/-- 第一因子の加群の射と第二因子の射から得る、右テンソルの加群の射。 -/
def tensorRightMap {E E' : Mod C M} (f : E ⟶ E') {X Y : C} (g : X ⟶ Y) :
    tensorRightObj M E X ⟶ tensorRightObj M E' Y :=
  Mod.Hom.mk' (f.hom ⊗ₘ g) (by
    have hf : γ[M,E.X] ≫ f.hom = M ◁ f.hom ≫ γ[M,E'.X] := IsModHom.smul_hom
    change ((α_ M E.X X).inv ≫ γ[M,E.X] ▷ X) ≫ (f.hom ⊗ₘ g) =
      M ◁ (f.hom ⊗ₘ g) ≫ (α_ M E'.X Y).inv ≫ γ[M,E'.X] ▷ Y
    simp only [tensorHom_def, whiskerLeft_comp, Category.assoc]
    rw [← comp_whiskerRight_assoc, hf, comp_whiskerRight]
    rw [Category.assoc, ← whisker_exchange]
    rw [associator_inv_naturality_right_assoc, associator_inv_naturality_middle_assoc])

/-- 右テンソルの結合子は第一因子の加群作用と両立する。 -/
def tensorRightAssociator (E : Mod C M) (X Y : C) :
    tensorRightObj M (tensorRightObj M E X) Y ⟶ tensorRightObj M E (X ⊗ Y) :=
  Mod.Hom.mk' (α_ E.X X Y).hom (by
    change ((α_ M (E.X ⊗ X) Y).inv ≫
        ((α_ M E.X X).inv ≫ γ[M,E.X] ▷ X) ▷ Y) ≫ (α_ E.X X Y).hom =
      M ◁ (α_ E.X X Y).hom ≫ (α_ M E.X (X ⊗ Y)).inv ≫ γ[M,E.X] ▷ (X ⊗ Y)
    simp only [comp_whiskerRight, Category.assoc]
    rw [associator_naturality_left]
    change (α_ M (E.X ⊗ X) Y).inv ≫ (α_ M E.X X).inv ▷ Y ≫
        (α_ (M ⊗ E.X) X Y).hom ≫ γ[M,E.X] ▷ (X ⊗ Y) = _
    have h : (α_ M (E.X ⊗ X) Y).inv ≫ (α_ M E.X X).inv ▷ Y ≫
        (α_ (M ⊗ E.X) X Y).hom =
      M ◁ (α_ E.X X Y).hom ≫ (α_ M E.X (X ⊗ Y)).inv := by monoidal
    simpa only [Category.assoc] using
      congrArg (fun k => k ≫ γ[M,E.X] ▷ (X ⊗ Y)) h)

variable [BraidedCategory C] [IsCommMonObj M]

/-- 可換係数では左作用と右側へ移した作用が両立する。 -/
@[reassoc] lemma action_middle (E : Mod C M) :
    γ[M,E.X] ▷ M ≫ rightActionMap M E =
      (α_ M E.X M).hom ≫ M ◁ rightActionMap M E ≫ γ[M,E.X] := by
  simp only [rightActionMap, whiskerLeft_comp, Category.assoc]
  rw [BraidedCategory.braiding_naturality_left_assoc]
  have he : M ◁ γ[M,E.X] ≫ γ[M,E.X] =
      (α_ M M E.X).inv ≫ μ[M] ▷ E.X ≫ γ[M,E.X] :=
    ModObj.mul_smul_self_flip (M := M) E.X
  change (β_ (M ⊗ E.X) M).hom ≫ M ◁ γ[M,E.X] ≫ γ[M,E.X] = _
  nth_rw 1 [he]
  rw [BraidedCategory.braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, IsCommMonObj.mul_comm]
  rw [← he]

/-- 右側へ移した作用は可換係数の加群の射となる。 -/
def rightActionHom (E : Mod C M) : tensorRightObj M E M ⟶ E :=
  Mod.Hom.mk' (rightActionMap M E) (by
    change ((α_ M E.X M).inv ≫ γ[M,E.X] ▷ M) ≫ rightActionMap M E =
      M ◁ rightActionMap M E ≫ γ[M,E.X]
    rw [Category.assoc, action_middle, Iso.inv_hom_id_assoc])

end SerrePositivity.MonoidalBalancedTensor
end

end TensorRightModule

/-! ## BalancedTensorModule（旧 SerrePositivity/CategoryTheory/Monoidal/BalancedTensorModule.lean） -/

/-! # 可換モノイド上の釣り合いテンソル積の加群作用

釣り合い関係式を加群の射へ持ち上げ、基礎対象の余等化子へ作用を降ろす。
作用の法則は加群の余極限の一般論から得る。
-/

@[expose] public section BalancedTensorModule
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (M : C) [MonObj M] [IsCommMonObj M]

/-- 釣り合い関係式の左辺は加群の射となる。 -/
def relationLeftHom (E F : Mod C M) :
    tensorRightObj M (tensorRightObj M E M) F.X ⟶ tensorRightObj M E F.X :=
  Mod.Hom.mk' (relationLeft M E F) (by
    change γ[M,(tensorRightObj M (tensorRightObj M E M) F.X).X] ≫ relationLeft M E F =
      M ◁ relationLeft M E F ≫ γ[M,(tensorRightObj M E F.X).X]
    have h : γ[M,(tensorRightObj M (tensorRightObj M E M) F.X).X] ≫
        (rightActionMap M E ⊗ₘ 𝟙 F.X) =
      M ◁ (rightActionMap M E ⊗ₘ 𝟙 F.X) ≫ γ[M,(tensorRightObj M E F.X).X] :=
      IsModHom.smul_hom (A := M) (f := (tensorRightMap M (rightActionHom M E) (𝟙 F.X)).hom)
    simpa only [tensorHom_id, relationLeft] using h)

/-- 釣り合い関係式の右辺は加群の射となる。 -/
def relationRightHom (E F : Mod C M) :
    tensorRightObj M (tensorRightObj M E M) F.X ⟶ tensorRightObj M E F.X :=
  Mod.Hom.mk' (relationRight M E F) (by
    change γ[M,(tensorRightObj M (tensorRightObj M E M) F.X).X] ≫ relationRight M E F =
      M ◁ relationRight M E F ≫ γ[M,(tensorRightObj M E F.X).X]
    have h : γ[M,(tensorRightObj M (tensorRightObj M E M) F.X).X] ≫
        ((α_ E.X M F.X).hom ≫ (𝟙 E.X ⊗ₘ γ[M,F.X])) =
      M ◁ ((α_ E.X M F.X).hom ≫ (𝟙 E.X ⊗ₘ γ[M,F.X])) ≫
        γ[M,(tensorRightObj M E F.X).X] :=
      IsModHom.smul_hom (A := M)
        (f := (tensorRightAssociator M E M F.X ≫ tensorRightMap M (𝟙 E) γ[M,F.X]).hom)
    simpa only [id_tensorHom, relationRight] using h)

/-- 釣り合いテンソル積を作る加群圏の平行射の図式。 -/
def moduleDiagram (E F : Mod C M) : WalkingParallelPair ⥤ Mod C M :=
  parallelPair (relationLeftHom M E F) (relationRightHom M E F)

/-- 平行射の忘却像は既存の釣り合い関係式の図式。 -/
def underlyingDiagramIso (E F : Mod C M) :
    moduleDiagram M E F ⋙ Mod.forget M ≅ parallelPair (relationLeft M E F) (relationRight M E F) :=
  NatIso.ofComponents (fun j => by cases j <;> exact Iso.refl _) (by
    rintro j k f
    cases f with
    | left => simp [moduleDiagram, relationLeftHom]
    | right => simp [moduleDiagram, relationRightHom]
    | id j => cases j <;> simp [moduleDiagram] <;> rfl)

variable [HasCoequalizers C]

/-- 加群図式の忘却像に対する、既存の釣り合い商の余錐。 -/
def underlyingCocone (E F : Mod C M) : Cocone (moduleDiagram M E F ⋙ Mod.forget M) :=
  (Cocone.precompose (underlyingDiagramIso M E F).hom).obj
    (Cofork.ofπ (projection M E F) (projection_condition M E F))

/-- 既存の釣り合い商の余錐は忘却像の余極限。 -/
def underlyingCoconeIsColimit (E F : Mod C M) : IsColimit (underlyingCocone M E F) :=
  (IsColimit.precomposeHomEquiv (underlyingDiagramIso M E F)
    (Cofork.ofπ (projection M E F) (projection_condition M E F))).symm
      (coequalizerIsCoequalizer (relationLeft M E F) (relationRight M E F))

/-- 忘却像の余錐の標準包含は既存の商への標準射。 -/
@[simp] lemma underlyingCocone_ι_one (E F : Mod C M) :
    (underlyingCocone M E F).ι.app WalkingParallelPair.one = projection M E F := by
  simp [underlyingCocone, underlyingDiagramIso]

variable [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]

/-- 釣り合い商上へ作用を降ろした内部加群。 -/
def moduleObj (E F : Mod C M) : Mod C M :=
  MonoidalModuleColimits.colimitObj M (moduleDiagram M E F) (underlyingCocone M E F)
    (underlyingCoconeIsColimit M E F)

/-- 構成した加群の基礎対象は既存の釣り合い商そのもの。 -/
lemma moduleObj_underlying (E F : Mod C M) : (moduleObj M E F).X = obj M E F := rfl

/-- 商の作用は標準射を介して第一因子の作用と両立する。 -/
@[reassoc] lemma projection_action (E F : Mod C M) :
    M ◁ projection M E F ≫ γ[M,(moduleObj M E F).X] =
      (α_ M E.X F.X).inv ≫ γ[M,E.X] ▷ F.X ≫ projection M E F := by
  have h := MonoidalModuleColimits.colimitSmul_ι M (moduleDiagram M E F)
    (underlyingCocone M E F) (underlyingCoconeIsColimit M E F) WalkingParallelPair.one
  change M ◁ (underlyingCocone M E F).ι.app WalkingParallelPair.one ≫
      γ[M,(moduleObj M E F).X] =
    γ[M,(tensorRightObj M E F.X).X] ≫
      (underlyingCocone M E F).ι.app WalkingParallelPair.one at h
  rw [underlyingCocone_ι_one] at h
  change M ◁ projection M E F ≫ γ[M,(moduleObj M E F).X] =
    ((α_ M E.X F.X).inv ≫ γ[M,E.X] ▷ F.X) ≫ projection M E F at h
  simpa only [Category.assoc] using h

/-- 既存の商の射は、降下した加群作用と両立する。 -/
def moduleMap {E E' F F' : Mod C M} (f : E ⟶ E') (g : F ⟶ F') :
    moduleObj M E F ⟶ moduleObj M E' F' :=
  Mod.Hom.mk' (map M f g) (by
    change γ[M,(moduleObj M E F).X] ≫ map M f g =
      M ◁ map M f g ≫ γ[M,(moduleObj M E' F').X]
    have : Epi (M ◁ projection M E F) := inferInstanceAs
      (Epi ((tensorLeft M).map (coequalizer.π (relationLeft M E F) (relationRight M E F))))
    apply (cancel_epi (M ◁ projection M E F)).1
    rw [projection_action_assoc, projection_map, ← whiskerLeft_comp_assoc,
      projection_map, whiskerLeft_comp, Category.assoc, projection_action]
    have h : γ[M,(tensorRightObj M E F.X).X] ≫ (f.hom ⊗ₘ g.hom) =
        M ◁ (f.hom ⊗ₘ g.hom) ≫ γ[M,(tensorRightObj M E' F'.X).X] :=
      IsModHom.smul_hom (A := M) (f := (tensorRightMap M f g.hom).hom)
    change ((α_ M E.X F.X).inv ≫ γ[M,E.X] ▷ F.X) ≫ (f.hom ⊗ₘ g.hom) =
      M ◁ (f.hom ⊗ₘ g.hom) ≫ ((α_ M E'.X F'.X).inv ≫ γ[M,E'.X] ▷ F'.X) at h
    simpa only [Category.assoc] using congrArg (fun k => k ≫ projection M E' F') h)

/-- 釣り合いテンソル積を加群圏に値を取る二変数関手へまとめる。 -/
def moduleBifunctor : Mod C M × Mod C M ⥤ Mod C M where
  obj EF := moduleObj M EF.1 EF.2
  map fg := moduleMap M fg.1 fg.2
  map_id EF := Mod.hom_ext _ _ (map_id M EF.1 EF.2)
  map_comp fg gh := Mod.hom_ext _ _ (map_comp M fg.1 gh.1 fg.2 gh.2)

/-- 釣り合い射が第一因子の加群作用と両立するとき、加群の射として降ろせる。 -/
def moduleDesc {E F G : Mod C M} (f : BalancedMap M E F G.X)
    (hf : (α_ M E.X F.X).inv ≫ γ[M,E.X] ▷ F.X ≫ f.val =
      M ◁ f.val ≫ γ[M,G.X]) : moduleObj M E F ⟶ G :=
  Mod.Hom.mk' (desc M f) (by
    change γ[M,(moduleObj M E F).X] ≫ desc M f = M ◁ desc M f ≫ γ[M,G.X]
    have : Epi (M ◁ projection M E F) := inferInstanceAs
      (Epi ((tensorLeft M).map (coequalizer.π (relationLeft M E F) (relationRight M E F))))
    apply (cancel_epi (M ◁ projection M E F)).1
    rw [projection_action_assoc, projection_desc, ← whiskerLeft_comp_assoc, projection_desc]
    exact hf)

/-- 加群の射として降下しても、基礎対象の降下は変わらない。 -/
lemma moduleDesc_hom {E F G : Mod C M} (f : BalancedMap M E F G.X)
    (hf : (α_ M E.X F.X).inv ≫ γ[M,E.X] ▷ F.X ≫ f.val =
      M ◁ f.val ≫ γ[M,G.X]) : (moduleDesc M f hf).hom = desc M f := rfl

end SerrePositivity.MonoidalBalancedTensor
end

end BalancedTensorModule

/-! ## BalancedTensorIterated（旧 SerrePositivity/CategoryTheory/Monoidal/BalancedTensorIterated.lean） -/

/-! # 釣り合い商のテンソルによる保存と反復テンソルの標準射 -/

@[expose] public section BalancedTensorIterated
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (M : C) [MonObj M] [HasCoequalizers C]

section Right

variable (E F : Mod C M) (X : C)
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

/-- 右テンソルした商の標準射はエピ射。 -/
instance projection_whiskerRight_epi : Epi (projection M E F ▷ X) :=
  inferInstanceAs (Epi ((tensorRight X).map
    (coequalizer.π (relationLeft M E F) (relationRight M E F))))

/-- 右テンソル後の釣り合い条件を満たす射を、右テンソルした商へ降ろす。 -/
def descRight {Y : C} (f : (E.X ⊗ F.X) ⊗ X ⟶ Y)
    (h : relationLeft M E F ▷ X ≫ f = relationRight M E F ▷ X ≫ f) :
    obj M E F ⊗ X ⟶ Y :=
  (PreservesCoequalizer.iso (tensorRight X) (relationLeft M E F) (relationRight M E F)).inv ≫
    coequalizer.desc f h

/-- 右テンソル後の降下は標準射上で指定した射に一致する。 -/
@[reassoc (attr := simp)] lemma projection_descRight {Y : C} (f : (E.X ⊗ F.X) ⊗ X ⟶ Y)
    (h : relationLeft M E F ▷ X ≫ f = relationRight M E F ▷ X ≫ f) :
    projection M E F ▷ X ≫ descRight M E F X f h = f :=
  map_π_preserves_coequalizer_inv_desc (tensorRight X) _ _ f h

end Right

section Left

variable (X : C) (E F : Mod C M)
  [PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]

/-- 左テンソルした商の標準射はエピ射。 -/
instance projection_whiskerLeft_epi : Epi (X ◁ projection M E F) :=
  inferInstanceAs (Epi ((tensorLeft X).map
    (coequalizer.π (relationLeft M E F) (relationRight M E F))))

/-- 左テンソル後の釣り合い条件を満たす射を、左テンソルした商へ降ろす。 -/
def descLeft {Y : C} (f : X ⊗ (E.X ⊗ F.X) ⟶ Y)
    (h : X ◁ relationLeft M E F ≫ f = X ◁ relationRight M E F ≫ f) :
    X ⊗ obj M E F ⟶ Y :=
  (PreservesCoequalizer.iso (tensorLeft X) (relationLeft M E F) (relationRight M E F)).inv ≫
    coequalizer.desc f h

/-- 左テンソル後の降下は標準射上で指定した射に一致する。 -/
@[reassoc (attr := simp)] lemma projection_descLeft {Y : C} (f : X ⊗ (E.X ⊗ F.X) ⟶ Y)
    (h : X ◁ relationLeft M E F ≫ f = X ◁ relationRight M E F ≫ f) :
    X ◁ projection M E F ≫ descLeft M X E F f h = f :=
  map_π_preserves_coequalizer_inv_desc (tensorLeft X) _ _ f h

end Left

variable [IsCommMonObj M]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]

/-- 標準射は第一因子から得るテンソル加群の作用と両立する。 -/
def projectionModuleHom (E F : Mod C M) : tensorRightObj M E F.X ⟶ moduleObj M E F :=
  Mod.Hom.mk' (projection M E F) (by
    change ((α_ M E.X F.X).inv ≫ γ[M,E.X] ▷ F.X) ≫ projection M E F =
      M ◁ projection M E F ≫ γ[M,(moduleObj M E F).X]
    rw [Category.assoc, projection_action])

/-- 商の右作用を、第二因子の右作用と標準射で計算する。 -/
@[reassoc] lemma projection_rightAction (E F : Mod C M) :
    projection M E F ▷ M ≫ rightActionMap M (moduleObj M E F) =
      (α_ E.X F.X M).hom ≫ E.X ◁ rightActionMap M F ≫ projection M E F := by
  rw [rightActionMap]
  erw [BraidedCategory.braiding_naturality_left_assoc, projection_action]
  rw [BraidedCategory.braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  slice_lhs 4 5 => rw [← comp_whiskerRight]
  change (α_ E.X F.X M).hom ≫ E.X ◁ (β_ F.X M).hom ≫ (α_ E.X M F.X).inv ≫
      rightActionMap M E ▷ F.X ≫ projection M E F = _
  have h := projection_condition M E F
  change rightActionMap M E ▷ F.X ≫ projection M E F =
    ((α_ E.X M F.X).hom ≫ E.X ◁ γ[M,F.X]) ≫ projection M E F at h
  rw [h, Category.assoc, Iso.inv_hom_id_assoc]
  simp only [rightActionMap, whiskerLeft_comp, Category.assoc]

/-- 左結合した三重テンソルへの、三つの因子からの標準射。 -/
def tripleLeftProjection (E F G : Mod C M) :
    (E.X ⊗ F.X) ⊗ G.X ⟶ obj M (moduleObj M E F) G :=
  projection M E F ▷ G.X ≫ projection M (moduleObj M E F) G

/-- 右結合した三重テンソルへの、三つの因子からの標準射。 -/
def tripleRightProjection (E F G : Mod C M) :
    E.X ⊗ (F.X ⊗ G.X) ⟶ obj M E (moduleObj M F G) :=
  E.X ◁ projection M F G ≫ projection M E (moduleObj M F G)

/-- 右結合した三重テンソルの標準射はエピ射。 -/
instance tripleRightProjection_epi (E F G : Mod C M) :
    Epi (tripleRightProjection M E F G) := by
  unfold tripleRightProjection
  infer_instance

/-- 左結合の標準射は三つの加群の射と両立する。 -/
@[reassoc] lemma tripleLeftProjection_map {E E' F F' G G' : Mod C M}
    (f : E ⟶ E') (g : F ⟶ F') (h : G ⟶ G') :
    tripleLeftProjection M E F G ≫ map M (moduleMap M f g) h =
      ((f.hom ⊗ₘ g.hom) ⊗ₘ h.hom) ≫ tripleLeftProjection M E' F' G' := by
  rw [tripleLeftProjection, Category.assoc, projection_map]
  change projection M E F ▷ G.X ≫ (map M f g ⊗ₘ h.hom) ≫
    projection M (moduleObj M E' F') G' = _
  simp only [tensorHom_def, Category.assoc]
  rw [← comp_whiskerRight_assoc, projection_map, comp_whiskerRight, Category.assoc,
    ← whisker_exchange_assoc]
  simp only [tripleLeftProjection, tensorHom_def]

/-- 右結合の標準射は三つの加群の射と両立する。 -/
@[reassoc] lemma tripleRightProjection_map {E E' F F' G G' : Mod C M}
    (f : E ⟶ E') (g : F ⟶ F') (h : G ⟶ G') :
    tripleRightProjection M E F G ≫ map M f (moduleMap M g h) =
      (f.hom ⊗ₘ (g.hom ⊗ₘ h.hom)) ≫ tripleRightProjection M E' F' G' := by
  rw [tripleRightProjection, Category.assoc, projection_map]
  change E.X ◁ projection M F G ≫ (f.hom ⊗ₘ map M g h) ≫
    projection M E' (moduleObj M F' G') = _
  simp only [tensorHom_def', Category.assoc]
  rw [← whiskerLeft_comp_assoc, projection_map, whiskerLeft_comp, Category.assoc,
    whisker_exchange_assoc]
  simp only [tripleRightProjection, tensorHom_def']

variable [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

/-- 左結合した三重テンソルの標準射はエピ射。 -/
instance tripleLeftProjection_epi (E F G : Mod C M) :
    Epi (tripleLeftProjection M E F G) := by
  unfold tripleLeftProjection
  infer_instance

end SerrePositivity.MonoidalBalancedTensor
end

end BalancedTensorIterated

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.5.2.1" (partial := special) "仮定：通常の対称モノイダル圏の可換内部モノイド A と必要な余等化子およびテンソルによる保存条件（Lean が強い：通常圏に限る）。結論：内部左加群に組紐から右作用を入れ、その作用で平衡化した相対テンソルを積とする対称モノイダル構造を構成する（この仮定での HA の結論の一部に一致）。(1) の通常圏の場合と (2) のテンソル公式に対応し、∞ オペラッド間のモノイダル比較は含まれない。"] _root_.SerrePositivity.MonoidalBalancedTensor.moduleObj
attribute [cite HA "4.5.2.1" (partial := special) "仮定：通常の対称モノイダル圏の可換内部モノイド A と必要な余等化子およびテンソルによる保存条件（Lean が強い：通常圏に限る）。結論：内部左加群に組紐から右作用を入れ、その作用で平衡化した相対テンソルを積とする対称モノイダル構造を構成する（この仮定での HA の結論の一部に一致）。(1) の通常圏の場合と (2) のテンソル公式に対応し、∞ オペラッド間のモノイダル比較は含まれない。"] _root_.SerrePositivity.MonoidalBalancedTensor.rightActionMap
