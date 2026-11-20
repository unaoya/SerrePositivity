module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.Monoidal
public import SerrePositivity.Spectra.SymmetricSpectrum.Tensor
public import SerrePositivity.Spectra.SymmetricSpectrum.Sphere

/-! # 球面上のテンソル積の右単位比較

正則加群との釣り合いテンソル積の自然同型を球面へ特殊化する。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (action)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 球面スペクトルを右側に置くテンソル積の単位同型。 -/
def sphereTensorRightUnit (E : SymmetricSpectrum.{u}) : sphereTensor E sphere ≅ E :=
  MonoidalBalancedTensor.rightUnitIso sphereSequence.{u} E

/-- 右単位同型は標準射上で右側へ移した球面作用に一致する。 -/
@[reassoc] lemma tensorProjection_rightUnit (E : SymmetricSpectrum.{u}) :
    tensorProjection E sphere ≫ (sphereTensorRightUnit E).hom.hom =
      (β_ E.X sphereSequence.{u}).hom ≫ action E :=
  MonoidalBalancedTensor.projection_rightUnitHom sphereSequence.{u} E

/-- 右単位同型の逆射は球面の単位を挿入して商へ射影する。 -/
lemma sphereTensorRightUnit_inv (E : SymmetricSpectrum.{u}) :
    (sphereTensorRightUnit E).inv.hom =
      (ρ_ E.X).inv ≫ E.X ◁ sphereUnitHom.{u} ≫ tensorProjection E sphere := rfl

/-- 右単位同型はスペクトルの射に関して自然。 -/
lemma sphereTensorRightUnit_naturality {E E' : SymmetricSpectrum.{u}} (f : E ⟶ E') :
    sphereTensorMap f (𝟙 sphere) ≫ (sphereTensorRightUnit E').hom =
      (sphereTensorRightUnit E).hom ≫ f :=
  MonoidalBalancedTensor.rightUnit_naturality sphereSequence.{u} f

/-- 球面スペクトルを右側に固定したテンソル積の関手。 -/
def sphereRightTensorFunctor : SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  MonoidalBalancedTensor.regularRightTensorFunctor sphereSequence.{u}

/-- 球面スペクトルとの右テンソル積は恒等関手と自然同型。 -/
def sphereTensorRightUnitNatIso : sphereRightTensorFunctor.{u} ≅ 𝟭 SymmetricSpectrum.{u} :=
  MonoidalBalancedTensor.rightUnitNatIso sphereSequence.{u}

end SerrePositivity.SymmetricSpectrum
