module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.Monoidal
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorRightUnit
public import SerrePositivity.Spectra.SymmetricSpectrum.Sphere

/-! # 球面上のテンソル積の左単位比較

正則加群との釣り合いテンソル積の自然同型を球面へ特殊化する。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (action)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 球面スペクトルを左側に置くテンソル積の単位同型。 -/
def sphereTensorLeftUnit (E : SymmetricSpectrum.{u}) : sphereTensor sphere E ≅ E :=
  MonoidalBalancedTensor.leftUnitIso sphereSequence.{u} E

/-- 左単位同型は標準射上で球面作用に一致する。 -/
@[reassoc] lemma tensorProjection_leftUnit (E : SymmetricSpectrum.{u}) :
    tensorProjection sphere E ≫ (sphereTensorLeftUnit E).hom.hom =
      action E :=
  MonoidalBalancedTensor.projection_leftUnitHom sphereSequence.{u} E

/-- 左単位同型の逆射は球面の単位を挿入して商へ射影する。 -/
lemma sphereTensorLeftUnit_inv (E : SymmetricSpectrum.{u}) :
    (sphereTensorLeftUnit E).inv.hom =
      (λ_ E.X).inv ≫ sphereUnitHom.{u} ▷ E.X ≫ tensorProjection sphere E := rfl

/-- 左単位同型はスペクトルの射に関して自然。 -/
lemma sphereTensorLeftUnit_naturality {E E' : SymmetricSpectrum.{u}} (f : E ⟶ E') :
    sphereTensorMap (𝟙 sphere) f ≫ (sphereTensorLeftUnit E').hom =
      (sphereTensorLeftUnit E).hom ≫ f :=
  MonoidalBalancedTensor.leftUnit_naturality sphereSequence.{u} f

/-- 球面スペクトルを左側に固定したテンソル積の関手。 -/
def sphereLeftTensorFunctor : SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  MonoidalBalancedTensor.regularLeftTensorFunctor sphereSequence.{u}

/-- 球面スペクトルとの左テンソル積は恒等関手と自然同型。 -/
def sphereTensorLeftUnitNatIso : sphereLeftTensorFunctor.{u} ≅ 𝟭 SymmetricSpectrum.{u} :=
  MonoidalBalancedTensor.leftUnitNatIso sphereSequence.{u}

/-- 球面スペクトル自身では左右の単位比較が一致する。 -/
lemma sphereTensorUnit_agree :
    sphereTensorLeftUnit sphere.{u} = sphereTensorRightUnit sphere.{u} := by
  apply Iso.ext
  apply Mod.hom_ext
  apply tensorSequence_hom_ext
  rw [tensorProjection_leftUnit, tensorProjection_rightUnit]
  exact (MonoidalBalancedTensor.rightActionMap_regular sphereSequence.{u}).symm

end SerrePositivity.SymmetricSpectrum
