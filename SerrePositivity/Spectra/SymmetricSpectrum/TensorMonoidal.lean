module

public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorMonoidal
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorPentagon
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorTriangle

/-! # 球面上の対称スペクトルのモノイダル構造

釣り合いテンソル積と球面単位のモノイダル構造を登録する。
交換同型のhexagonと対称構造への登録はTensorHexagon・TensorSymmetricで行う。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 球面上の釣り合いテンソル積による対称スペクトルのモノイダル構造。 -/
instance sphereTensorMonoidalCategory : MonoidalCategory SymmetricSpectrum.{u} :=
  MonoidalBalancedTensor.monoidalCategory sphereSequence.{u}

/-- 登録したスペクトルのテンソル積は既存の球面上のテンソル積。 -/
lemma tensorObj_eq_sphereTensor (E F : SymmetricSpectrum.{u}) : E ⊗ F = sphereTensor E F := rfl

/-- 登録したスペクトルのテンソル射は既存のテンソル積の射。 -/
lemma tensorHom_eq_sphereTensorMap {E E' F F' : SymmetricSpectrum.{u}}
    (f : E ⟶ E') (g : F ⟶ F') : f ⊗ₘ g = sphereTensorMap f g := rfl

/-- 登録したテンソル単位は球面スペクトル。 -/
lemma tensorUnit_eq_sphere : 𝟙_ SymmetricSpectrum.{u} = sphere := rfl

/-- 登録した結合子は構成済みの結合同型。 -/
lemma associator_eq_sphereTensorAssociator (E F G : SymmetricSpectrum.{u}) :
    α_ E F G = sphereTensorAssociator E F G := rfl

/-- 登録した左単位同型は構成済みの球面の左単位比較。 -/
lemma leftUnitor_eq_sphereTensorLeftUnit (E : SymmetricSpectrum.{u}) :
    λ_ E = sphereTensorLeftUnit E := rfl

/-- 登録した右単位同型は構成済みの球面の右単位比較。 -/
lemma rightUnitor_eq_sphereTensorRightUnit (E : SymmetricSpectrum.{u}) :
    ρ_ E = sphereTensorRightUnit E := rfl

end SerrePositivity.SymmetricSpectrum
