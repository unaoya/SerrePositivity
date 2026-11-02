module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.Monoidal
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorAssociator
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorLeftUnit

/-! # 球面上のテンソル積のtriangle整合性

結合同型と左右の単位比較から得られる二つの経路の一致を証明する。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory
open SerrePositivity.PointedSimplicialSet

/-- 球面を中央に置いたテンソル積の結合同型と左右の単位比較はtriangleを満たす。 -/
lemma sphereTensorTriangle (E F : SymmetricSpectrum.{u}) :
    (sphereTensorAssociator E sphere F).hom ≫
        sphereTensorMap (𝟙 E) (sphereTensorLeftUnit F).hom =
      sphereTensorMap (sphereTensorRightUnit E).hom (𝟙 F) :=
  MonoidalBalancedTensor.triangle sphereSequence.{u} E F

/-- triangleを逆結合同型から始める経路の一致として書く。 -/
lemma sphereTensorTriangle_inv (E F : SymmetricSpectrum.{u}) :
    (sphereTensorAssociator E sphere F).inv ≫
        sphereTensorMap (sphereTensorRightUnit E).hom (𝟙 F) =
      sphereTensorMap (𝟙 E) (sphereTensorLeftUnit F).hom :=
  MonoidalBalancedTensor.triangle_inv sphereSequence.{u} E F

end SerrePositivity.SymmetricSpectrum
