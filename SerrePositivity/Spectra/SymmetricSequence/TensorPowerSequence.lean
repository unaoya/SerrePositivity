module

public import SerrePositivity.CategoryTheory.Monoidal.PowerBijectionFunctor
public import SerrePositivity.Spectra.SymmetricSequence.Basic

/-!
# 反復テンソルを対称列として扱う

共通の全単射圏上の関手を、convolution を備える対称列の型へ接続する。
各段の対象と作用を、既存の反復テンソル・置換作用と比較する。
-/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.SymmetricSequence

open CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 任意の対象の反復テンソルから得る対称列。 -/
def tensorPowerSequence (X : C) : SymmetricSequence C := TensorPowers.bijectionFunctor X

/-- 各段の対象は既存の反復テンソル。 -/
lemma tensorPowerSequence_level (X : C) (n : ℕ) :
    level (tensorPowerSequence X) n = TensorPowers.power X n := rfl

/-- 置換の像は既存の対称群作用。 -/
lemma tensorPowerSequence_map_permutation (X : C) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (tensorPowerSequence X).map (FiniteBijection.permutation n σ) =
      (TensorPowers.permutationAction X n σ).asIso.hom :=
  TensorPowers.bijectionFunctor_map_permutation X n σ

/-- 対称列から取り出す各段の作用も、構成した置換作用に一致する。 -/
lemma tensorPowerSequence_levelAction (X : C) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ((levelAction (tensorPowerSequence X) n).ρ σ).asHom =
      (TensorPowers.permutationAction X n σ).asIso.hom :=
  tensorPowerSequence_map_permutation X n σ

end SerrePositivity.SymmetricSequence
