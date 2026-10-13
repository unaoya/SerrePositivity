module

public import SerrePositivity.CategoryTheory.Monoidal.ModuleLimits

/-! # 内部加群の余極限

左テンソルが図式の形の余極限を保存する場合、忘却関手はその余極限を創出する。
閉構造自体は仮定せず、余極限保存を明示的な仮定として用いる。
-/

@[expose] public section

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
