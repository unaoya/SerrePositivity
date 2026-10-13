module

public import SerrePositivity.CategoryTheory.Monoidal.PermutationAction
public import SerrePositivity.Spectra.SymmetricSequence.SpherePowers

/-!
# 円の反復 smash への全置換作用

一般の反復テンソルの対称群作用を円へ特殊化する。
全単射圏上の関手への接続は `SphereSequence` で行う。
ブロック置換に関する連結の整合性は `SpherePowerCoherence` で証明する。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.PointedSimplicialSet

open CategoryTheory

/-- 第n段の円の反復 smash への対称群の作用。 -/
def spherePermutationAction (n : ℕ) :
    Equiv.Perm (Fin n) →* Aut (spherePower.{u} n) :=
  TensorPowers.permutationAction (circle : PointedSimplicialSet.{u}) n

/-- 標準の隣接互換は既存の円の隣接交換へ送られる。 -/
lemma spherePermutationAction_adjacent (n : ℕ) (i : Fin n) :
    spherePermutationAction.{u} (n + 1) (Coxeter.adjacentTransposition i) =
      Aut.of (spherePowerAdjacentIso.{u} n i) :=
  TensorPowers.permutationAction_adjacent (circle : PointedSimplicialSet.{u}) n i

/-- 置換の積と反復 smash の射の合成の対応。 -/
lemma spherePermutationAction_mul (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    (spherePermutationAction.{u} n (σ * τ)).asIso.hom =
      (spherePermutationAction.{u} n τ).asIso.hom ≫
        (spherePermutationAction.{u} n σ).asIso.hom :=
  TensorPowers.permutationAction_mul (circle : PointedSimplicialSet.{u}) n σ τ

end SerrePositivity.PointedSimplicialSet
