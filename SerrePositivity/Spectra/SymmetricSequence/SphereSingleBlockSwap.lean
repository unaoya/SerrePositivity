module

public import SerrePositivity.Spectra.SymmetricSequence.TensorPowerSingleBlockSwap
public import SerrePositivity.Spectra.SymmetricSequence.SphereCommutativity

/-! # 球面の第1段と任意の段のブロック交換

第1段を左右のどちらに置く場合も、braiding・連結・添字のブロック交換の合成を比較する。
一般の二つの正次数のブロック全体の交換はまだ含まない。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.PointedSimplicialSet

open CategoryTheory CategoryTheory.MonoidalCategory

/-- 球面の第1段を左側に置くブロック全体の交換と連結の両立。 -/
lemma sphere_swap_one_left (n : ℕ) :
    (β_ (spherePower.{u} 1) (spherePower.{u} n)).hom ≫
        (spherePowerAppendIso.{u} n 1).hom ≫
        sphereSequence.{u}.map
          (FiniteBijection.sumSymmetry (FiniteBijection.of n) (FiniteBijection.of 1)).hom =
      (spherePowerAppendIso.{u} 1 n).hom :=
  SymmetricSequence.tensorPower_swap_one_left (circle : PointedSimplicialSet.{u}) n

/-- 球面の第1段を右側に置くブロック全体の交換と連結の両立。 -/
lemma sphere_swap_one_right (n : ℕ) :
    (β_ (spherePower.{u} n) (spherePower.{u} 1)).hom ≫
        (spherePowerAppendIso.{u} 1 n).hom ≫
        sphereSequence.{u}.map
          (FiniteBijection.sumSymmetry (FiniteBijection.of 1) (FiniteBijection.of n)).hom =
      (spherePowerAppendIso.{u} n 1).hom :=
  SymmetricSequence.tensorPower_swap_one_right (circle : PointedSimplicialSet.{u}) n

end SerrePositivity.PointedSimplicialSet
