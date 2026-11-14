module


public meta import SerrePositivity.Util.Citation
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Limits.Creates

/-!
# Monoidal.Mod.Limits

## 概要
関連する圏論の構成と補題をまとめる。各構成の詳細は以下の元モジュールの説明を参照。

## 方針
元の宣言と証明を保持し、依存順に section を分けて配置する。

## 規約
公開宣言名・名前空間・宇宙変数の意味を変更しない。元の module docstring は各節に保存する。

## 使われ方
旧モジュールの利用元は `SerrePositivity.CategoryTheory.Monoidal.Mod.Limits` を直接 import する。
-/

/-! ## ModuleLimits（旧 SerrePositivity/CategoryTheory/Monoidal/ModuleLimits.lean） -/

/-! # 内部加群の極限

モノイド対象M上の加群の極限を、基礎圏の極限上に構成する。
テンソル積が極限を保存するという仮定は必要ない。
-/

@[expose] public section ModuleLimits
universe v u w w'

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalModuleLimits

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (M : C) [MonObj M]

/-- underlying射の逆射も加群作用と両立する。 -/
instance forget_reflectsIsomorphisms : (Mod.forget (D := C) M).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    have : IsIso f.hom := inferInstanceAs (IsIso ((Mod.forget (D := C) M).map f))
    let : IsModHom M (asIso f.hom).hom := f.isModHom
    let : IsModHom M (inv f.hom) := inferInstanceAs (IsModHom M (asIso f.hom).inv)
    let g : Y ⟶ X := Mod.Hom.mk' (inv f.hom)
    exact ⟨⟨g, by apply Mod.hom_ext; simp [g], by apply Mod.hom_ext; simp [g]⟩⟩

variable {J : Type w} [Category.{w'} J] (F : J ⥤ Mod C M)
  (c : Cone (F ⋙ Mod.forget M)) (hc : IsLimit c)

/-- 極限の作用を定義するための錐。 -/
def actionCone : Cone (F ⋙ Mod.forget M) where
  pt := M ⊗ c.pt
  π.app j := M ◁ c.π.app j ≫ γ[M, (F.obj j).X]
  π.naturality i j f := by
    change 𝟙 (M ⊗ c.pt) ≫ (M ◁ c.π.app j ≫ γ[M, (F.obj j).X]) =
      (M ◁ c.π.app i ≫ γ[M, (F.obj i).X]) ≫ (F.map f).hom
    rw [Category.id_comp]
    symm
    have hf : γ[M, (F.obj i).X] ≫ (F.map f).hom =
        M ◁ (F.map f).hom ≫ γ[M, (F.obj j).X] := IsModHom.smul_hom
    rw [Category.assoc, hf, ← whiskerLeft_comp_assoc]
    exact congrArg (fun k => M ◁ k ≫ γ[M, (F.obj j).X]) (c.w f)

/-- 基礎圏の極限に誘導される加群作用。 -/
@[instance_reducible] def limitAction : ModObj M c.pt where
  smul := hc.lift (actionCone M F c)
  one_smul := by
    change η[M] ▷ c.pt ≫ hc.lift (actionCone M F c) = (λ_ c.pt).hom
    apply hc.hom_ext
    intro j
    simp only [Category.assoc, IsLimit.fac, actionCone]
    rw [← whisker_exchange_assoc, ModObj.one_smul_self,
      leftUnitor_naturality]
  mul_smul := by
    change μ[M] ▷ c.pt ≫ hc.lift (actionCone M F c) =
      (α_ M M c.pt).hom ≫ M ◁ hc.lift (actionCone M F c) ≫ hc.lift (actionCone M F c)
    apply hc.hom_ext
    intro j
    simp only [Category.assoc, IsLimit.fac, actionCone]
    rw [← whisker_exchange_assoc, ModObj.mul_smul_self]
    rw [← whiskerLeft_comp_assoc, hc.fac]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [associator_naturality_right_assoc]

/-- 基礎圏の極限対象を持つ内部加群。 -/
def limitObj : Mod C M :=
  letI := limitAction M F c hc
  ⟨c.pt⟩

/-- 誘導された作用は各射影と両立する。 -/
@[reassoc] lemma limitAction_π (j : J) :
    γ[M, (limitObj M F c hc).X] ≫ c.π.app j =
      M ◁ c.π.app j ≫ γ[M, (F.obj j).X] := hc.fac (actionCone M F c) j

/-- 加群圏へ持ち上げた極限錐。 -/
def limitCone : Cone F where
  pt := limitObj M F c hc
  π.app j := Mod.Hom.mk' (c.π.app j) (limitAction_π M F c hc j)
  π.naturality i j f := by
    apply Mod.hom_ext
    simpa using (c.w f).symm

/-- 持ち上げた錐の忘却像は元の錐。 -/
def forgetLimitConeIso : (Mod.forget M).mapCone (limitCone M F c hc) ≅ c :=
  Cone.ext (Iso.refl _) (by intro j; simp [limitCone])

/-- 持ち上げた錐の極限の普遍性。 -/
def limitConeIsLimit : IsLimit (limitCone M F c hc) where
  lift s := Mod.Hom.mk' (hc.lift ((Mod.forget M).mapCone s)) (by
    change γ[M, s.pt.X] ≫ hc.lift ((Mod.forget M).mapCone s) =
      M ◁ hc.lift ((Mod.forget M).mapCone s) ≫ γ[M, (limitObj M F c hc).X]
    apply hc.hom_ext
    intro j
    simp only [Category.assoc, hc.fac, limitAction_π]
    rw [← whiskerLeft_comp_assoc, hc.fac]
    exact IsModHom.smul_hom (A := M) (f := (s.π.app j).hom))
  fac s j := Mod.hom_ext _ _ (hc.fac ((Mod.forget M).mapCone s) j)
  uniq s m h := by
    apply Mod.hom_ext
    apply hc.hom_ext
    intro j
    change m.hom ≫ c.π.app j = hc.lift ((Mod.forget M).mapCone s) ≫ c.π.app j
    rw [hc.fac]
    exact congrArg Mod.Hom.hom (h j)

/-- 忘却関手は、基礎圏の任意の極限錐を加群の極限錐へ持ち上げる。 -/
def limitConeLiftsToLimit : LiftsToLimit F (Mod.forget M) c hc where
  liftedCone := limitCone M F c hc
  validLift := forgetLimitConeIso M F c hc
  makesLimit := limitConeIsLimit M F c hc

instance forget_createsLimit : CreatesLimit F (Mod.forget M) :=
  createsLimitOfReflectsIso (limitConeLiftsToLimit M F)

instance forget_createsLimitsOfShape : CreatesLimitsOfShape J (Mod.forget (D := C) M) where

instance forget_createsLimitsOfSize :
    CreatesLimitsOfSize.{w', w} (Mod.forget (D := C) M) where

instance [HasLimitsOfShape J C] : HasLimitsOfShape J (Mod C M) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Mod.forget M)

instance [HasLimitsOfSize.{w', w} C] : HasLimitsOfSize.{w', w} (Mod C M) where

end SerrePositivity.MonoidalModuleLimits
end

end ModuleLimits

/-! ## ModuleTransport（旧 SerrePositivity/CategoryTheory/Monoidal/ModuleTransport.lean） -/

/-! # 基礎対象の同型による内部加群の作用の移送 -/

@[expose] public section ModuleTransport
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
end

end ModuleTransport

/-! ## ModuleColimits（旧 SerrePositivity/CategoryTheory/Monoidal/ModuleColimits.lean） -/

/-! # 内部加群の余極限

左テンソルが図式の形の余極限を保存する場合、忘却関手はその余極限を創出する。
閉構造自体は仮定せず、余極限保存を明示的な仮定として用いる。
-/

@[expose] public section ModuleColimits
universe v u w w'

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalModuleColimits

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (M : C) [MonObj M]
  {J : Type w} [Category.{w'} J] [∀ X : C, PreservesColimitsOfShape J (tensorLeft X)]
  (F : J ⥤ Mod C M) (c : Cocone (F ⋙ Mod.forget M)) (hc : IsColimit c)

/-- 余極限の作用を定義するための余錐。 -/
def actionCocone : Cocone ((F ⋙ Mod.forget M) ⋙ tensorLeft M) where
  pt := c.pt
  ι.app j := γ[M, (F.obj j).X] ≫ c.ι.app j
  ι.naturality i j f := by
    change (M ◁ (F.map f).hom) ≫ (γ[M, (F.obj j).X] ≫ c.ι.app j) =
      (γ[M, (F.obj i).X] ≫ c.ι.app i) ≫ 𝟙 c.pt
    have hf : γ[M, (F.obj i).X] ≫ (F.map f).hom =
        M ◁ (F.map f).hom ≫ γ[M, (F.obj j).X] := IsModHom.smul_hom
    erw [Category.comp_id, ← Category.assoc, ← hf, Category.assoc]
    exact congrArg (fun k => γ[M, (F.obj i).X] ≫ k) (c.w f)

/-- テンソル積の余極限保存から得られる作用の射。 -/
def colimitSmul : M ⊗ c.pt ⟶ c.pt :=
  (isColimitOfPreserves (tensorLeft M) hc).desc (actionCocone M F c)

/-- 誘導された作用は各包含と両立する。 -/
@[reassoc] lemma colimitSmul_ι (j : J) :
    M ◁ c.ι.app j ≫ colimitSmul M F c hc = γ[M, (F.obj j).X] ≫ c.ι.app j :=
  (isColimitOfPreserves (tensorLeft M) hc).fac (actionCocone M F c) j

/-- 基礎圏の余極限に誘導される加群作用。 -/
@[instance_reducible] def colimitAction : ModObj M c.pt where
  smul := colimitSmul M F c hc
  one_smul := by
    change η[M] ▷ c.pt ≫ colimitSmul M F c hc = (λ_ c.pt).hom
    apply (isColimitOfPreserves (tensorLeft (𝟙_ C)) hc).hom_ext
    intro j
    change (𝟙_ C) ◁ c.ι.app j ≫ (η[M] ▷ c.pt ≫ colimitSmul M F c hc) =
      (𝟙_ C) ◁ c.ι.app j ≫ (λ_ c.pt).hom
    erw [whisker_exchange_assoc, colimitSmul_ι,
      ← Category.assoc, ModObj.one_smul_self, leftUnitor_naturality]
    rfl
  mul_smul := by
    change μ[M] ▷ c.pt ≫ colimitSmul M F c hc =
      (α_ M M c.pt).hom ≫ M ◁ colimitSmul M F c hc ≫ colimitSmul M F c hc
    apply (isColimitOfPreserves (tensorLeft (M ⊗ M)) hc).hom_ext
    intro j
    change (M ⊗ M) ◁ c.ι.app j ≫ (μ[M] ▷ c.pt ≫ colimitSmul M F c hc) =
      (M ⊗ M) ◁ c.ι.app j ≫ (α_ M M c.pt).hom ≫
        M ◁ colimitSmul M F c hc ≫ colimitSmul M F c hc
    erw [whisker_exchange_assoc, colimitSmul_ι,
      ← Category.assoc, ModObj.mul_smul_self]
    erw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc, colimitSmul_ι]
    simp only [whiskerLeft_comp, Category.assoc, colimitSmul_ι]
    rfl

/-- 基礎圏の余極限対象を持つ内部加群。 -/
def colimitObj : Mod C M :=
  letI := colimitAction M F c hc
  ⟨c.pt⟩

/-- 加群圏へ持ち上げた余極限余錐。 -/
def colimitCocone : Cocone F where
  pt := colimitObj M F c hc
  ι.app j := Mod.Hom.mk' (c.ι.app j) (colimitSmul_ι M F c hc j).symm
  ι.naturality i j f := by
    apply Mod.hom_ext
    simpa using c.w f

/-- 持ち上げた余錐の忘却像は元の余錐。 -/
def forgetColimitCoconeIso : (Mod.forget M).mapCocone (colimitCocone M F c hc) ≅ c :=
  Cocone.ext (Iso.refl _) (by intro j; simp [colimitCocone])

/-- 持ち上げた余錐の余極限の普遍性。 -/
def colimitCoconeIsColimit : IsColimit (colimitCocone M F c hc) where
  desc s := Mod.Hom.mk' (hc.desc ((Mod.forget M).mapCocone s)) (by
    change colimitSmul M F c hc ≫ hc.desc ((Mod.forget M).mapCocone s) =
      M ◁ hc.desc ((Mod.forget M).mapCocone s) ≫ γ[M, s.pt.X]
    apply (isColimitOfPreserves (tensorLeft M) hc).hom_ext
    intro j
    change (M ◁ c.ι.app j) ≫ (colimitSmul M F c hc ≫
      hc.desc ((Mod.forget M).mapCocone s)) =
      (M ◁ c.ι.app j) ≫ (M ◁ hc.desc ((Mod.forget M).mapCocone s) ≫ γ[M, s.pt.X])
    rw [← Category.assoc, colimitSmul_ι, Category.assoc, hc.fac,
      ← Category.assoc, ← whiskerLeft_comp, hc.fac]
    exact IsModHom.smul_hom (A := M) (f := (s.ι.app j).hom))
  fac s j := Mod.hom_ext _ _ (hc.fac ((Mod.forget M).mapCocone s) j)
  uniq s m h := by
    apply Mod.hom_ext
    apply hc.hom_ext
    intro j
    change c.ι.app j ≫ m.hom = c.ι.app j ≫ hc.desc ((Mod.forget M).mapCocone s)
    rw [hc.fac]
    exact congrArg Mod.Hom.hom (h j)

/-- 忘却関手は基礎圏の余極限余錐を加群の余極限余錐へ持ち上げる。 -/
def colimitCoconeLiftsToColimit : LiftsToColimit F (Mod.forget M) c hc where
  liftedCocone := colimitCocone M F c hc
  validLift := forgetColimitCoconeIso M F c hc
  makesColimit := colimitCoconeIsColimit M F c hc

instance forget_createsColimit : CreatesColimit F (Mod.forget M) :=
  createsColimitOfReflectsIso (colimitCoconeLiftsToColimit M F)

instance forget_createsColimitsOfShape : CreatesColimitsOfShape J (Mod.forget (D := C) M) where

instance [HasColimitsOfShape J C] : HasColimitsOfShape J (Mod C M) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (Mod.forget M)

end SerrePositivity.MonoidalModuleColimits
end

end ModuleColimits

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.2.3.3" (partial := special) "仮定：通常のモノイダル圏の内部モノイドと小さい通常圏の加群図式（Lean は通常圏の自己作用に限る。スカラー制限は通常の環の場合）。結論：基礎圏の極限を内部加群の極限へ持ち上げ、忘却が極限を生成する。通常の環ではスカラー制限も極限を保つ（通常圏での各成分に一致）。一般の左テンソル ∞ 圏は含まれない。"] _root_.SerrePositivity.MonoidalModuleLimits.forget_createsLimitsOfShape
attribute [cite HA "4.2.3.3" (partial := special) "仮定：通常のモノイダル圏の内部モノイドと小さい通常圏の加群図式（Lean は通常圏の自己作用に限る。スカラー制限は通常の環の場合）。結論：基礎圏の極限を内部加群の極限へ持ち上げ、忘却が極限を生成する。通常の環ではスカラー制限も極限を保つ（通常圏での各成分に一致）。一般の左テンソル ∞ 圏は含まれない。"] _root_.SerrePositivity.MonoidalModuleLimits.limitConeLiftsToLimit
attribute [cite HA "4.2.3.5" (partial := special) "仮定：通常のモノイダル圏の内部モノイドと、左テンソルが添字の余極限を保つ通常圏の図式（Lean は通常圏の自己作用に限る）。結論：基礎圏の余極限を内部加群の余極限へ持ち上げる。通常の環ではアーベル群への忘却が余極限を保存・反映する（通常圏での二成分に一致）。一般の左テンソル ∞ 圏は含まれない。"] _root_.SerrePositivity.MonoidalModuleColimits.colimitCoconeLiftsToColimit
