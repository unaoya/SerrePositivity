module

public import SerrePositivity.Spectra.SymmetricSequence.TensorPowerSequence
public import SerrePositivity.Spectra.SymmetricSequence.SpherePermutationAction
public import SerrePositivity.Spectra.SymmetricSequence.Pointed

/-!
# 円の反復 smash による球面対称列

全単射圏上の反復テンソル関手を円に適用する。
各段とその作用は既存の `spherePower` と `spherePermutationAction` をそのまま使用する。
convolution に関する可換モノイド構造は `SphereCommMonoid` で登録する。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.PointedSimplicialSet

open CategoryTheory

/-- 円の反復 smash による球面対称列。 -/
def sphereSequence : PointedSymmetricSequence.{u} :=
  SymmetricSequence.tensorPowerSequence (circle : PointedSimplicialSet.{u})

/-- 球面対称列の各段は円の反復 smash。 -/
lemma sphereSequence_level (n : ℕ) :
    SymmetricSequence.level sphereSequence.{u} n = spherePower.{u} n := rfl

/-- 球面対称列の置換の像は既存の作用。 -/
lemma sphereSequence_map_permutation (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    sphereSequence.{u}.map (FiniteBijection.permutation n σ) =
      (spherePermutationAction.{u} n σ).asIso.hom :=
  SymmetricSequence.tensorPowerSequence_map_permutation (circle : PointedSimplicialSet.{u}) n σ

/-- 対称列から取り出した作用も既存の作用に一致する。 -/
lemma sphereSequence_levelAction (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ((SymmetricSequence.levelAction sphereSequence.{u} n).ρ σ).asHom =
      (spherePermutationAction.{u} n σ).asIso.hom :=
  sphereSequence_map_permutation n σ

end SerrePositivity.PointedSimplicialSet
