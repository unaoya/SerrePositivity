module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Limits.Creates

/-! # 内部加群の極限

モノイド対象M上の加群の極限を、基礎圏の極限上に構成する。
テンソル積が極限を保存するという仮定は必要ない。
-/

@[expose] public section

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
