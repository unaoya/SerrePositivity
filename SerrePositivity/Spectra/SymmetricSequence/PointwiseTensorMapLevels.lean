module

public import SerrePositivity.Spectra.SymmetricSequence.PointwiseTensorEvaluation
public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroModuleMap

/-! # 転置と前合成による各段のテンソル射の計算 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open CategoryTheory.Limits
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- 生成対象の射を各段で通常のテンソル射にするという法則。 -/
def pointwiseTensorPostLevelLaw {X Y : C} (f : X ⟶ Y) (A : SymmetricSequence C)
    (h : (pointwiseTensorFunctor X).obj A ⟶ (pointwiseTensorFunctor Y).obj A)
    (q : ℕ) : Prop :=
  h.app (FiniteBijection.of q) = f ▷ level A q

/-- 転置・前合成・逆転置の各段の法則から、生成対象の通常のテンソル射を得る。 -/
lemma pointwiseTensorPostLevelLaw_of_curry {X Y : C} (f : X ⟶ Y)
    (A : SymmetricSequence C) {B D : SymmetricSequence C}
    (b : B ≅ unshiftedInternalHom Y ((pointwiseTensorFunctor Y).obj A))
    (a : D ≅ unshiftedInternalHom X ((pointwiseTensorFunctor Y).obj A))
    (k : A ⟶ B) (p : B ⟶ D)
    (h : (pointwiseTensorFunctor X).obj A ⟶ (pointwiseTensorFunctor Y).obj A) (q : ℕ)
    (hk : k.app (FiniteBijection.of q) ≫ b.hom.app (FiniteBijection.of q) =
      curry (𝟙 (Y ⊗ level A q)))
    (hp : unshiftedInternalHomMapLevelLaw f (𝟙 ((pointwiseTensorFunctor Y).obj A))
      (b.inv ≫ p ≫ a.hom) q)
    (hh : h.app (FiniteBijection.of q) =
      uncurry ((k ≫ p).app (FiniteBijection.of q) ≫ a.hom.app (FiniteBijection.of q))) :
    pointwiseTensorPostLevelLaw f A h q := by
  have hp' : b.inv.app (FiniteBijection.of q) ≫ p.app (FiniteBijection.of q) ≫
      a.hom.app (FiniteBijection.of q) = (pre f).app (Y ⊗ level A q) := by
    change b.inv.app (FiniteBijection.of q) ≫ p.app (FiniteBijection.of q) ≫
      a.hom.app (FiniteBijection.of q) =
        (pre f).app (Y ⊗ level A q) ≫ (ihom X).map (𝟙 _) at hp
    rw [CategoryTheory.Functor.map_id, Category.comp_id] at hp
    exact hp
  have hc := congrArg (fun t =>
    (k.app (FiniteBijection.of q) ≫ b.hom.app (FiniteBijection.of q)) ≫ t) hp'
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc] at hc
  have hkr := congrArg (fun t => t ≫ (pre f).app (Y ⊗ level A q)) hk
  simp only [Category.assoc] at hkr
  have hcc := hc.trans hkr
  unfold pointwiseTensorPostLevelLaw
  rw [hh]
  erw [NatTrans.comp_app, Category.assoc]
  erw [hcc, uncurry_pre_app, uncurry_curry, Category.comp_id]
  rfl

/-- 両変数のテンソル射が各段の通常のテンソル積の射になるという法則。 -/
def pointwiseTensorBimapLevelLaw {X Y : C} (f : X ⟶ Y)
    {A B : SymmetricSequence C} (g : A ⟶ B)
    (h : (pointwiseTensorFunctor X).obj A ⟶ (pointwiseTensorFunctor Y).obj B) (q : ℕ) :
    Prop := h.app (FiniteBijection.of q) = f ⊗ₘ g.app (FiniteBijection.of q)

omit [MonoidalClosed C] in
/-- 生成対象の射の法則と値域の関手の射の公式を両変数の法則へまとめる。 -/
lemma pointwiseTensorBimapLevelLaw_of_post {X Y : C} (f : X ⟶ Y)
    {A B : SymmetricSequence C} (g : A ⟶ B)
    (p : (pointwiseTensorFunctor X).obj A ⟶ (pointwiseTensorFunctor Y).obj A) (q : ℕ)
    (hp : pointwiseTensorPostLevelLaw f A p q) :
    pointwiseTensorBimapLevelLaw f g (p ≫ (pointwiseTensorFunctor Y).map g) q := by
  change p.app (FiniteBijection.of q) ≫ Y ◁ g.app (FiniteBijection.of q) = _
  rw [hp, tensorHom_def]
  rfl


variable [SymmetricCategory C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)]
  [∀ Z : SymmetricSequence C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
  [∀ Z : SymmetricSequence C, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
  (M : SymmetricSequence C) [MonObj M] [IsCommMonObj M]

/-- 係数加群の生成対象の射の各段の通常のテンソルの法則。 -/
def pointwiseTensorPostModuleLevelLaw {X Y : C} (f : X ⟶ Y)
    (A : Mod (SymmetricSequence C) M)
    (h : pointwiseTensorModule M X A ⟶ pointwiseTensorModule M Y A) (q : ℕ) : Prop :=
  pointwiseTensorPostLevelLaw f A.X h.hom q

omit [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)]
  [∀ Z : SymmetricSequence C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
  [∀ Z : SymmetricSequence C, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
  [IsCommMonObj M] in
/-- 係数加群の転置・前合成・逆転置の法則を生成対象の射の法則へ接続する。 -/
lemma pointwiseTensorPostModuleLevelLaw_of_curry {X Y : C} (f : X ⟶ Y)
    (A : Mod (SymmetricSequence C) M) {B D : Mod (SymmetricSequence C) M}
    (b : B.X ≅ unshiftedInternalHom Y (pointwiseTensorModule M Y A).X)
    (a : D.X ≅ unshiftedInternalHom X (pointwiseTensorModule M Y A).X)
    (k : A ⟶ B) (p : B ⟶ D)
    (h : pointwiseTensorModule M X A ⟶ pointwiseTensorModule M Y A) (q : ℕ)
    (hk : pointwiseTensorCurryLevelLaw M Y b (𝟙 (pointwiseTensorModule M Y A)) k q)
    (hp : unshiftedInternalHomMapLevelLaw f (𝟙 (pointwiseTensorModule M Y A).X)
      (b.inv ≫ p.hom ≫ a.hom) q)
    (hh : pointwiseTensorUncurryLevelLaw M X a (k ≫ p) h q) :
    pointwiseTensorPostModuleLevelLaw M f A h q := by
  apply pointwiseTensorPostLevelLaw_of_curry f A.X b a k.hom p.hom h.hom q
  · exact hk
  · exact hp
  · exact hh

/-- 係数加群の両変数の射の各段の通常のテンソルの法則。 -/
def pointwiseTensorBimapModuleLevelLaw {X Y : C} (f : X ⟶ Y)
    {A B : Mod (SymmetricSequence C) M} (g : A ⟶ B)
    (h : pointwiseTensorModule M X A ⟶ pointwiseTensorModule M Y B) (q : ℕ) : Prop :=
  pointwiseTensorBimapLevelLaw f g.hom h.hom q

omit [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)]
  [∀ Z : SymmetricSequence C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
  [∀ Z : SymmetricSequence C, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
  [IsCommMonObj M] in
/-- 係数加群の生成対象の法則を、両変数の射の法則へまとめる。 -/
lemma pointwiseTensorBimapModuleLevelLaw_of_post {X Y : C} (f : X ⟶ Y)
    {A B : Mod (SymmetricSequence C) M} (g : A ⟶ B)
    (p : pointwiseTensorModule M X A ⟶ pointwiseTensorModule M Y A) (q : ℕ)
    (hp : pointwiseTensorPostModuleLevelLaw M f A p q) :
    pointwiseTensorBimapModuleLevelLaw M f g
      (p ≫ (pointwiseTensorModuleFunctor M Y).map g) q := by
  unfold pointwiseTensorBimapModuleLevelLaw
  rw [Mod.comp_hom', pointwiseTensorModuleFunctor_map_hom]
  exact pointwiseTensorBimapLevelLaw_of_post f g.hom p.hom q hp

end SerrePositivity.SymmetricSequence
