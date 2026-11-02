module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Permutation
public import SerrePositivity.Spectra.PointedSimplicialSet.Monoidal

/-!
# 円の反復 smash による球面対称列の各段

第0段を smash の単位とし、円を右に括って反復 smash する。
次数の連結同型、各位置の隣接交換とその関係式を、一般の反復テンソルから特殊化する。
まだ全ての置換作用を備えた対称列ではない。
境界商による単体的球面と定義上同じものとは扱わない。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.PointedSimplicialSet

open CategoryTheory CategoryTheory.MonoidalCategory

/-- 球面対称列に使う、円の n 回の smash。 -/
def spherePower (n : ℕ) : PointedSimplicialSet.{u} :=
  TensorPowers.power (circle : PointedSimplicialSet.{u}) n

@[simp] lemma spherePower_zero : spherePower.{u} 0 = (sphereZero : PointedSimplicialSet.{u}) := rfl

lemma spherePower_succ (n : ℕ) :
    spherePower.{u} (n + 1) =
      PointedObject.smash (circle : PointedSimplicialSet.{u}) (spherePower.{u} n) := rfl

/-- 第1段は単体的な円と同型。 -/
def spherePowerOneIso : spherePower.{u} 1 ≅ (circle : PointedSimplicialSet.{u}) :=
  TensorPowers.oneIso (circle : PointedSimplicialSet.{u})

/-- 第2段は円二つの smash と同型。 -/
def spherePowerTwoIso : spherePower.{u} 2 ≅ PointedObject.smash
    (circle : PointedSimplicialSet.{u}) circle :=
  whiskerLeftIso (circle : PointedSimplicialSet.{u}) spherePowerOneIso.{u}

/-- 二つの次数を連結して和次数へ送る同型。 -/
def spherePowerAppendIso (m n : ℕ) :
    PointedObject.smash (spherePower.{u} m) (spherePower.{u} n) ≅ spherePower.{u} (m + n) :=
  TensorPowers.appendIso (circle : PointedSimplicialSet.{u}) m n

/-- 円の反復 smash の最初の二因子の交換。 -/
def spherePowerSwapFirstIso (n : ℕ) :
    spherePower.{u} (n + 2) ≅ (spherePower.{u} (n + 2) : PointedSimplicialSet.{u}) :=
  TensorPowers.swapFirstIso (circle : PointedSimplicialSet.{u}) n

lemma spherePowerSwapFirstIso_involutive (n : ℕ) :
    (spherePowerSwapFirstIso n).hom ≫ (spherePowerSwapFirstIso n).hom =
      𝟙 (spherePower.{u} (n + 2) : PointedSimplicialSet.{u}) :=
  TensorPowers.swapFirstIso_involutive (circle : PointedSimplicialSet.{u}) n

/-- 円の反復 smash の任意の位置の隣接交換。 -/
def spherePowerAdjacentIso (n : ℕ) (i : Fin n) :
    spherePower.{u} (n + 1) ≅ spherePower.{u} (n + 1) :=
  TensorPowers.adjacentIso (circle : PointedSimplicialSet.{u}) n i

lemma spherePowerAdjacentIso_involutive (n : ℕ) (i : Fin n) :
    (spherePowerAdjacentIso.{u} n i).hom ≫ (spherePowerAdjacentIso.{u} n i).hom =
      𝟙 (spherePower.{u} (n + 1)) :=
  TensorPowers.adjacentIso_involutive (circle : PointedSimplicialSet.{u}) n i

lemma spherePowerAdjacentIso_commute (n : ℕ) (i j : Fin n) (h : i.val + 1 < j.val) :
    (spherePowerAdjacentIso.{u} n i).hom ≫ (spherePowerAdjacentIso.{u} n j).hom =
      (spherePowerAdjacentIso.{u} n j).hom ≫ (spherePowerAdjacentIso.{u} n i).hom :=
  TensorPowers.adjacentIso_commute (circle : PointedSimplicialSet.{u}) n i j h

lemma spherePowerAdjacentIso_braid (n : ℕ) (i : Fin n) :
    (spherePowerAdjacentIso.{u} (n + 1) i.castSucc).hom ≫
        (spherePowerAdjacentIso.{u} (n + 1) i.succ).hom ≫
        (spherePowerAdjacentIso.{u} (n + 1) i.castSucc).hom =
      (spherePowerAdjacentIso.{u} (n + 1) i.succ).hom ≫
        (spherePowerAdjacentIso.{u} (n + 1) i.castSucc).hom ≫
        (spherePowerAdjacentIso.{u} (n + 1) i.succ).hom :=
  TensorPowers.adjacentIso_braid (circle : PointedSimplicialSet.{u}) n i

end SerrePositivity.PointedSimplicialSet
