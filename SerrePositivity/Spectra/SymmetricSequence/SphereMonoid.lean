module

public import SerrePositivity.Spectra.SymmetricSequence.TensorPowerMonoid
public import SerrePositivity.Spectra.SymmetricSequence.SphereUnit

/-! # 球面対称列のモノイド構造

円の反復smashの対称列を、convolution上のモノイド対象としてまとめる。
ブロック全体の交換との比較と、可換モノイド構造はまだ含まない。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.PointedSimplicialSet

open CategoryTheory CategoryTheory.MonoidalCategory

/-- 球面対称列のconvolution全体の乗法の結合則。 -/
lemma sphere_associativity :
    (sphereMultiplication.{u} ▷ sphereSequence.{u}) ≫ sphereMultiplication.{u} =
      (α_ sphereSequence.{u} sphereSequence.{u} sphereSequence.{u}).hom ≫
        (sphereSequence.{u} ◁ sphereMultiplication.{u}) ≫ sphereMultiplication.{u} :=
  SymmetricSequence.tensorPower_associativity (circle : PointedSimplicialSet.{u})

/-- 構成済みの乗法・単位を持つ球面対称列のモノイド対象。 -/
instance sphereSequenceMonObj : MonObj sphereSequence.{u} :=
  SymmetricSequence.tensorPowerMonObj (circle : PointedSimplicialSet.{u})

/-- 球面対称列を、構成済みのモノイド構造とともにまとめる。 -/
def sphereMonoid : Mon PointedSymmetricSequence.{u} := ⟨sphereSequence.{u}⟩

/-- モノイド対象の underlying object は既存の球面対称列。 -/
lemma sphereMonoid_obj : sphereMonoid.{u}.X = sphereSequence.{u} := rfl

/-- 登録されたモノイドの単位射は既存の球面の単位射。 -/
lemma sphereMonoid_one : MonObj.one (X := sphereMonoid.{u}.X) = sphereUnitHom.{u} := rfl

/-- 登録されたモノイドの乗法は既存の球面の乗法。 -/
lemma sphereMonoid_mul : MonObj.mul (X := sphereMonoid.{u}.X) = sphereMultiplication.{u} := rfl

end SerrePositivity.PointedSimplicialSet
