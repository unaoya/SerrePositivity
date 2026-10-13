module

public import SerrePositivity.Spectra.SymmetricSequence.TensorPowerCommutativity
public import SerrePositivity.Spectra.SymmetricSequence.SphereMonoid

/-! # 球面対称列の可換性の帰着

乗法の可換性を、各次数の連結とブロック全体の交換の等式へ帰着する。
第0段を含む場合を証明する。一般の交換と可換性全体は `SphereCommMonoid` で証明する。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.PointedSimplicialSet

open CategoryTheory CategoryTheory.MonoidalCategory

/-- 球面の乗法の可換性は、各次数のブロック全体の交換との両立と同値。 -/
lemma sphere_commutativity_iff :
    (β_ sphereSequence.{u} sphereSequence.{u}).hom ≫ sphereMultiplication.{u} =
        sphereMultiplication.{u} ↔
      ∀ m n : ℕ,
        (β_ (spherePower.{u} m) (spherePower.{u} n)).hom ≫
          (spherePowerAppendIso.{u} n m).hom ≫
          sphereSequence.{u}.map
            (FiniteBijection.sumSymmetry (FiniteBijection.of n) (FiniteBijection.of m)).hom =
        (spherePowerAppendIso.{u} m n).hom :=
  SymmetricSequence.tensorPower_commutativity_iff (circle : PointedSimplicialSet.{u})

/-- 第0段を左側に置く場合の、球面の連結とブロック全体の交換の両立。 -/
lemma sphere_swap_zero_left (n : ℕ) :
    (β_ (spherePower.{u} 0) (spherePower.{u} n)).hom ≫
        (spherePowerAppendIso.{u} n 0).hom ≫
        sphereSequence.{u}.map
          (FiniteBijection.sumSymmetry (FiniteBijection.of n) (FiniteBijection.of 0)).hom =
      (spherePowerAppendIso.{u} 0 n).hom :=
  SymmetricSequence.tensorPower_swap_zero_left (circle : PointedSimplicialSet.{u}) n

/-- 第0段を右側に置く場合の、球面の連結とブロック全体の交換の両立。 -/
lemma sphere_swap_zero_right (n : ℕ) :
    (β_ (spherePower.{u} n) (spherePower.{u} 0)).hom ≫
        (spherePowerAppendIso.{u} 0 n).hom ≫
        sphereSequence.{u}.map
          (FiniteBijection.sumSymmetry (FiniteBijection.of 0) (FiniteBijection.of n)).hom =
      (spherePowerAppendIso.{u} n 0).hom :=
  SymmetricSequence.tensorPower_swap_zero_right (circle : PointedSimplicialSet.{u}) n

/-- 球面の乗法の可換性は、正次数どうしのブロック交換だけへ帰着する。 -/
lemma sphere_commutativity_iff_positive :
    (β_ sphereSequence.{u} sphereSequence.{u}).hom ≫ sphereMultiplication.{u} =
        sphereMultiplication.{u} ↔
      ∀ m n : ℕ,
        (β_ (spherePower.{u} (m + 1)) (spherePower.{u} (n + 1))).hom ≫
          (spherePowerAppendIso.{u} (n + 1) (m + 1)).hom ≫
          sphereSequence.{u}.map
            (FiniteBijection.sumSymmetry
              (FiniteBijection.of (n + 1)) (FiniteBijection.of (m + 1))).hom =
        (spherePowerAppendIso.{u} (m + 1) (n + 1)).hom :=
  SymmetricSequence.tensorPower_commutativity_iff_positive (circle : PointedSimplicialSet.{u})

end SerrePositivity.PointedSimplicialSet
