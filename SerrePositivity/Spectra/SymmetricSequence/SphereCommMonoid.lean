module

public import SerrePositivity.Spectra.SymmetricSequence.TensorPowerCommMonoid
public import SerrePositivity.Spectra.SymmetricSequence.SphereSingleBlockSwap

/-! # 球面対称列の可換モノイド構造

一般のブロック交換を円へ特殊化し、既存の球面対称列の乗法・単位を持つ可換モノイドを構成する。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.PointedSimplicialSet

open CategoryTheory CategoryTheory.MonoidalCategory

/-- 球面の全次数のブロック全体の交換と連結の両立。 -/
lemma sphere_block_swap (m n : ℕ) :
    (β_ (spherePower.{u} m) (spherePower.{u} n)).hom ≫
        (spherePowerAppendIso.{u} n m).hom ≫
        sphereSequence.{u}.map
          (FiniteBijection.sumSymmetry (FiniteBijection.of n) (FiniteBijection.of m)).hom =
      (spherePowerAppendIso.{u} m n).hom :=
  SymmetricSequence.tensorPower_block_swap (circle : PointedSimplicialSet.{u}) m n

/-- 球面対称列のconvolution全体の乗法の可換性。 -/
lemma sphere_commutativity :
    (β_ sphereSequence.{u} sphereSequence.{u}).hom ≫ sphereMultiplication.{u} =
      sphereMultiplication.{u} :=
  SymmetricSequence.tensorPower_commutativity (circle : PointedSimplicialSet.{u})

/-- 既存の球面対称列のモノイド構造に、可換性を登録する。 -/
instance sphereSequenceIsCommMonObj : IsCommMonObj sphereSequence.{u} :=
  SymmetricSequence.tensorPowerIsCommMonObj (circle : PointedSimplicialSet.{u})

/-- 既存の乗法・単位を持つ球面対称列の可換モノイド対象。 -/
def sphereCommMonoid : CommMon PointedSymmetricSequence.{u} := ⟨sphereSequence.{u}⟩

/-- 可換モノイド対象のunderlying objectは既存の球面対称列。 -/
lemma sphereCommMonoid_obj : sphereCommMonoid.{u}.X = sphereSequence.{u} := rfl

/-- 可換モノイド対象から可換性を忘れると、既存の球面モノイドになる。 -/
lemma sphereCommMonoid_toMon : sphereCommMonoid.{u}.toMon = sphereMonoid.{u} := rfl

/-- 可換モノイドの単位射は既存の球面の単位射。 -/
lemma sphereCommMonoid_one : MonObj.one (X := sphereCommMonoid.{u}.X) = sphereUnitHom.{u} := rfl

/-- 可換モノイドの乗法は既存の球面の乗法。 -/
lemma sphereCommMonoid_mul :
    MonObj.mul (X := sphereCommMonoid.{u}.X) = sphereMultiplication.{u} := rfl

end SerrePositivity.PointedSimplicialSet
