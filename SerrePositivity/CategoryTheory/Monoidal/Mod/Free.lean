module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Monoidal.Mod.Free

## 概要
関連する圏論の構成と補題をまとめる。各構成の詳細は以下の元モジュールの説明を参照。

## 方針
元の宣言と証明を保持し、依存順に section を分けて配置する。

## 規約
公開宣言名・名前空間・宇宙変数の意味を変更しない。元の module docstring は各節に保存する。

## 使われ方
旧モジュールの利用元は `SerrePositivity.CategoryTheory.Monoidal.Mod.Free` を直接 import する。
-/

/-! ## FreeModule（旧 SerrePositivity/CategoryTheory/Monoidal/FreeModule.lean） -/

/-! # モノイド対象上の自由内部加群と忘却関手の随伴

一般のモノイダル圏でM⊗Xを自由M加群にし、生成元によるHom同値から随伴を構成する。
対称構造・閉構造・余極限を仮定せず、スペクトルには依存しない。
-/

@[expose] public section FreeModule
universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalFreeModule

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (M : C) [MonObj M]

/-- テンソル積M⊗Xに、モノイドの乗法による自由加群の作用を与える。 -/
@[instance_reducible] def freeAction (X : C) : ModObj M (M ⊗ X) where
  smul := (α_ M M X).inv ≫ (μ[M] ▷ X)
  one_smul := by
    change η[M] ▷ (M ⊗ X) ≫ (α_ M M X).inv ≫ (μ[M] ▷ X) = (λ_ (M ⊗ X)).hom
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, MonObj.one_mul]
    monoidal
  mul_smul := by
    change μ[M] ▷ (M ⊗ X) ≫ (α_ M M X).inv ≫ (μ[M] ▷ X) =
      (α_ M M (M ⊗ X)).hom ≫ M ◁ ((α_ M M X).inv ≫ (μ[M] ▷ X)) ≫
        (α_ M M X).inv ≫ (μ[M] ▷ X)
    rw [associator_inv_naturality_left_assoc]
    rw [← comp_whiskerRight, MonObj.mul_assoc]
    simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
    rw [associator_inv_naturality_middle_assoc, pentagon_hom_inv_inv_inv_hom_assoc]
/-- 任意の対象から得る自由内部加群。 -/
def freeObj (X : C) : Mod C M :=
  letI := freeAction M X
  ⟨M ⊗ X⟩
/-- 対象の射が誘導する自由加群の射。 -/
def freeMap {X Y : C} (f : X ⟶ Y) : freeObj M X ⟶ freeObj M Y :=
  Mod.Hom.mk' (M ◁ f) (by
    change ((α_ M M X).inv ≫ μ[M] ▷ X) ≫ (M ◁ f) =
      M ◁ (M ◁ f) ≫ (α_ M M Y).inv ≫ μ[M] ▷ Y
    rw [Category.assoc, ← whisker_exchange, associator_inv_naturality_right_assoc])
/-- 自由加群への生成元の射。 -/
def generator (X : C) : X ⟶ (freeObj M X).X := (λ_ X).inv ≫ (η[M] ▷ X)
/-- 生成元から加群への射を、自由加群の射へ延長する。 -/
def lift (X : C) (E : Mod C M) (f : X ⟶ E.X) : freeObj M X ⟶ E :=
  Mod.Hom.mk' (M ◁ f ≫ γ[M, E.X]) (by
    change ((α_ M M X).inv ≫ μ[M] ▷ X) ≫ (M ◁ f ≫ γ[M,E.X]) =
      M ◁ (M ◁ f ≫ γ[M,E.X]) ≫ γ[M,E.X]
    simp only [Category.assoc, whiskerLeft_comp]
    rw [← whisker_exchange_assoc, ← associator_inv_naturality_right_assoc,
      ← ModObj.mul_smul_self_flip])
/-- 延長した射を生成元へ制限すると元の射になる。 -/
lemma generator_lift (X : C) (E : Mod C M) (f : X ⟶ E.X) :
    generator M X ≫ (lift M X E f).hom = f := by
  change ((λ_ X).inv ≫ (η[M] ▷ X)) ≫ (M ◁ f ≫ γ[M,E.X]) = f
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc,
    ModObj.one_smul_self, Iso.inv_hom_id, Category.comp_id]

/-- 生成元に係数を作用させると、自由加群の恒等射になる。 -/
lemma generator_action (X : C) :
    M ◁ generator M X ≫ γ[M,(freeObj M X).X] = 𝟙 (M ⊗ X) := by
  change M ◁ ((λ_ X).inv ≫ (η[M] ▷ X)) ≫ (α_ M M X).inv ≫ (μ[M] ▷ X) = _
  rw [whiskerLeft_comp, Category.assoc, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight, MonObj.mul_one]
  monoidal
/-- 自由加群の射は、生成元での値からの延長に等しい。 -/
lemma lift_generator (X : C) (E : Mod C M) (f : freeObj M X ⟶ E) :
    lift M X E (generator M X ≫ f.hom) = f := by
  apply Mod.hom_ext
  change (M ◁ (generator M X ≫ f.hom)) ≫ γ[M,E.X] = f.hom
  rw [whiskerLeft_comp, Category.assoc]
  erw [← IsModHom.smul_hom (A := M) (f := f.hom)]
  erw [← Category.assoc, generator_action, Category.id_comp]
/-- 自由加群からの射と、生成元からの射との同値。 -/
def freeHomEquiv (X : C) (E : Mod C M) :
    (freeObj M X ⟶ E) ≃ (X ⟶ E.X) where
  toFun f := generator M X ≫ f.hom
  invFun f := lift M X E f
  left_inv f := lift_generator M X E f
  right_inv f := generator_lift M X E f

/-- 自由内部加群を作る関手。 -/
def freeFunctor : C ⥤ Mod C M where
  obj X := freeObj M X
  map f := freeMap M f
  map_id X := by
    apply Mod.hom_ext
    exact whiskerLeft_id M X
  map_comp f g := by
    apply Mod.hom_ext
    exact whiskerLeft_comp M f g

/-- 自由加群関手と作用を忘れる関手の随伴。 -/
def freeForgetAdjunction : freeFunctor M ⊣ Mod.forget (D := C) M :=
  Adjunction.mkOfHomEquiv {
    homEquiv := freeHomEquiv M
    homEquiv_naturality_left_symm := by
      intro X Y E f g
      apply Mod.hom_ext
      change M ◁ (f ≫ g) ≫ γ[M,E.X] = (M ◁ f) ≫ (M ◁ g) ≫ γ[M,E.X]
      rw [whiskerLeft_comp, Category.assoc]
    homEquiv_naturality_right := by
      intro X E E' f g
      change generator M X ≫ (f.hom ≫ g.hom) = (generator M X ≫ f.hom) ≫ g.hom
      rw [Category.assoc] }
/-- 随伴の単位は生成元の射。 -/
lemma free_unit (X : C) : (freeForgetAdjunction M).unit.app X = generator M X := by
  change generator M X ≫ 𝟙 (M ⊗ X) = _
  erw [Category.comp_id]
/-- 随伴の余単位の underlying 射は加群作用。 -/
lemma free_counit (E : Mod C M) : ((freeForgetAdjunction M).counit.app E).hom = γ[M,E.X] := by
  change (M ◁ 𝟙 E.X) ≫ γ[M,E.X] = _
  rw [whiskerLeft_id, Category.id_comp]

end SerrePositivity.MonoidalFreeModule
end

end FreeModule
