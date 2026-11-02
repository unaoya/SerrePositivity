module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Blocks

public import SerrePositivity.Spectra.SymmetricSequence.SpherePermutationAction
public import SerrePositivity.Spectra.SymmetricSequence.SpherePowers

/-!
# 円の反復 smash の連結の整合性

一般のモノイダル圏で証明した単位・結合の整合性を円へ特殊化する。
左右ブロックの隣接交換と、任意のブロック置換に関する連結の同変性も含む。
ブロック全体を交換する対称性との比較はまだ含まない。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.PointedSimplicialSet

open CategoryTheory CategoryTheory.MonoidalCategory

/-- 円の反復 smash の連結の右単位。 -/
lemma spherePowerAppendIso_zero_right (n : ℕ) :
    (spherePowerAppendIso.{u} n 0).hom = (ρ_ (spherePower.{u} n)).hom :=
  TensorPowers.appendIso_zero_right (circle : PointedSimplicialSet.{u}) n

/-- 円の反復 smash の三次数の連結は結合子と両立する。 -/
lemma spherePowerAppendIso_associativity (l m n : ℕ) :
    ((spherePowerAppendIso.{u} l m).hom ▷ spherePower.{u} n) ≫
        (spherePowerAppendIso.{u} (l + m) n).hom ≫
        eqToHom (congrArg spherePower.{u} (Nat.add_assoc l m n)) =
      (α_ (spherePower.{u} l) (spherePower.{u} m) (spherePower.{u} n)).hom ≫
        (spherePower.{u} l ◁ (spherePowerAppendIso.{u} m n).hom) ≫
        (spherePowerAppendIso.{u} l (m + n)).hom :=
  TensorPowers.appendIso_associativity (circle : PointedSimplicialSet.{u}) l m n

/-- 右ブロックの隣接交換と円の連結の両立。 -/
lemma spherePowerAppendIso_adjacent_right (m n : ℕ) (i : Fin n) :
    (spherePower.{u} m ◁ (spherePowerAdjacentIso.{u} n i).hom) ≫
        (spherePowerAppendIso.{u} m (n + 1)).hom =
      (spherePowerAppendIso.{u} m (n + 1)).hom ≫
        (spherePowerAdjacentIso.{u} (m + n) (i.natAdd m)).hom :=
  TensorPowers.appendIso_adjacent_right (circle : PointedSimplicialSet.{u}) m n i

/-- 左ブロックの隣接交換と円の連結の両立。次数の移送を含む。 -/
lemma spherePowerAppendIso_adjacent_left (m n : ℕ) (i : Fin m) :
    ((spherePowerAdjacentIso.{u} m i).hom ▷ spherePower.{u} n) ≫
        (spherePowerAppendIso.{u} (m + 1) n).hom ≫
        eqToHom (congrArg spherePower.{u} (Nat.succ_add m n)) =
      (spherePowerAppendIso.{u} (m + 1) n).hom ≫
        eqToHom (congrArg spherePower.{u} (Nat.succ_add m n)) ≫
        (spherePowerAdjacentIso.{u} (m + n) (i.castAdd n)).hom :=
  TensorPowers.appendIso_adjacent_left (circle : PointedSimplicialSet.{u}) m n i

/-- 左右の任意の置換に関する、円の反復 smash の連結の同変性。 -/
lemma spherePowerAppendIso_block_permutation (m n : ℕ)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    ((spherePermutationAction.{u} m σ).asIso.hom ⊗ₘ
        (spherePermutationAction.{u} n τ).asIso.hom) ≫
        (spherePowerAppendIso.{u} m n).hom =
      (spherePowerAppendIso.{u} m n).hom ≫
        (spherePermutationAction.{u} (m + n) (FiniteBijection.blockEquiv σ τ)).asIso.hom :=
  TensorPowers.appendIso_block_permutation (circle : PointedSimplicialSet.{u}) m n σ τ

end SerrePositivity.PointedSimplicialSet
