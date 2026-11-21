module

public import SerrePositivity.Spectra.SymmetricSequence.TensorPowerCommMonoid
public import Mathlib.CategoryTheory.Monoidal.Mod

/-! # Symmetric spectra over an arbitrary category and suspension coordinate

The objects are Mathlib internal modules over the tensor-power commutative
monoid in Day convolution. No model structure is required to define them.
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity
variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [CategoryTheory.Limits.HasColimitsOfSize.{0, 0} C]

/-- Internal modules over Sym(K) in the Day convolution category. -/
abbrev GeneralSymmetricSpectrum (K : C) :=
  Mod (SymmetricSequence C) (SymmetricSequence.tensorPowerSequence K)

namespace GeneralSymmetricSpectrum

variable {C} {K : C}
open SymmetricSequence

/-- 対称スペクトルの underlying 対称列。 -/
abbrev underlying (E : GeneralSymmetricSpectrum C K) : SymmetricSequence C := E.X
/-- 球面の加群作用を忘れる関手。 -/
def forget (K : C) : GeneralSymmetricSpectrum C K ⥤ SymmetricSequence C :=
  Mod.forget (D := SymmetricSequence C) (tensorPowerSequence K)
instance forget_faithful : (forget (C := C) K).Faithful where
  map_injective := fun h ↦ Mod.hom_ext _ _ h
/-- 対称スペクトルの第n段の基点付き単体的集合。 -/
abbrev level (E : GeneralSymmetricSpectrum C K) (n : ℕ) : C :=
  SymmetricSequence.level E.X n
/-- convolutionによる球面対称列の加群作用。 -/
def action (E : GeneralSymmetricSpectrum C K) :
    (tensorPowerSequence K) ⊗ E.X ⟶ E.X :=
  ModObj.smul (M := (tensorPowerSequence K)) (X := E.X)
/-- 加群作用の結合則。 -/
lemma action_assoc (E : GeneralSymmetricSpectrum C K) :
    (tensorPowerMultiplication K) ▷ E.X ≫ action E =
      (α_ (tensorPowerSequence K) (tensorPowerSequence K) E.X).hom ≫
        (tensorPowerSequence K) ◁ action E ≫ action E :=
  ModObj.mul_smul_self (tensorPowerSequence K) E.X
/-- スペクトルの射は球面の作用と両立する。 -/
@[reassoc] lemma action_hom {E F : GeneralSymmetricSpectrum C K} (f : E ⟶ F) :
    action E ≫ f.hom = (tensorPowerSequence K) ◁ f.hom ≫ action F :=
  IsModHom.smul_hom (A := (tensorPowerSequence K)) (f := f.hom)
/-- スペクトルの射の成分は、次数の等式による移送と両立する。 -/
lemma hom_index_eq {E F : GeneralSymmetricSpectrum C K} (f : E ⟶ F)
    {m n : ℕ} (h : m = n) :
    eqToHom (congrArg (level E) h) ≫ f.hom.app (FiniteBijection.of n) =
      f.hom.app (FiniteBijection.of m) ≫ eqToHom (congrArg (level F) h) := by
  subst n
  simp

/-- スペクトルの射の第n段の成分。 -/
def levelMap {E F : GeneralSymmetricSpectrum C K} (f : E ⟶ F) (n : ℕ) : level E n ⟶ level F n :=
  f.hom.app (FiniteBijection.of n)

/-- 合成の各段の成分は成分の合成。 -/
lemma levelMap_comp {E F G : GeneralSymmetricSpectrum C K} (f : E ⟶ F) (g : F ⟶ G) (n : ℕ) :
    levelMap (f ≫ g) n = levelMap f n ≫ levelMap g n := rfl

/-- スペクトルの射は各段の成分で決まる。 -/
lemma hom_ext {E F : GeneralSymmetricSpectrum C K} (f g : E ⟶ F)
    (h : ∀ n, levelMap f n = levelMap g n) : f = g := by
  apply Mod.hom_ext
  apply NatTrans.ext
  funext A
  rw [← FiniteBijection.of_card A]
  exact h (FiniteBijection.card A)

end GeneralSymmetricSpectrum
end SerrePositivity
