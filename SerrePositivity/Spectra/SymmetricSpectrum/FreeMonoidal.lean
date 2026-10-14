module

public import SerrePositivity.CategoryTheory.Monoidal.FreeModuleMonoidal
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorSymmetric
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorFreePair

/-! # 自由スペクトル関手の強モノイダル構造

自由球面加群関手の単位・テンソル比較を登録し、結合・左右の単位・交換との両立を供給する。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 自由スペクトル関手は強モノイダル関手。 -/
instance freeFunctorMonoidal : freeFunctor.{u}.Monoidal :=
  MonoidalBalancedTensor.freeFunctorMonoidal sphereSequence.{u}

/-- 自由スペクトル関手はbraidingも保存する。 -/
instance freeFunctorBraided : freeFunctor.{u}.Braided :=
  MonoidalBalancedTensor.freeFunctorBraided sphereSequence.{u}

/-- 球面スペクトルと単位対称列から作る自由スペクトルの比較同型。 -/
def freeUnitComparison : sphere.{u} ≅ freeObj (𝟙_ PointedSymmetricSequence.{u}) :=
  (MonoidalBalancedTensor.freeUnitIso sphereSequence.{u}).symm

/-- 自由関手の単位比較の逆射は基礎対称列の右単位同型。 -/
lemma freeUnitComparison_inv :
    freeUnitComparison.{u}.inv.hom = (ρ_ sphereSequence.{u}).hom :=
  MonoidalBalancedTensor.freeUnitIso_hom sphereSequence.{u}

/-- 単位対称列の生成元は単位比較を介して球面の単位へ送られる。 -/
lemma generator_freeUnitComparison :
    generator (𝟙_ PointedSymmetricSequence.{u}) ≫ freeUnitComparison.{u}.inv.hom =
      sphereUnitHom.{u} := MonoidalBalancedTensor.generator_freeUnit sphereSequence.{u}

/-- 登録した自由スペクトル関手の単位比較は構成済みの単位同型。 -/
lemma freeFunctor_unitIso : Functor.Monoidal.εIso freeFunctor.{u} = freeUnitComparison := by
  apply Iso.ext
  rfl

/-- 登録した自由スペクトル関手のテンソル比較は構成済みの二自由加群の比較。 -/
lemma freeFunctor_tensorIso (X Y : PointedSymmetricSequence.{u}) :
    Functor.Monoidal.μIso freeFunctor X Y = sphereTensorFreePair X Y := by
  apply Iso.ext
  rfl

end SerrePositivity.SymmetricSpectrum
