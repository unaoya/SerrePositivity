module

public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorHexagon
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorAssociator
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorSymmetry

/-! # 球面上のテンソル積のhexagon整合性 -/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory
open SerrePositivity.PointedSimplicialSet

/-- 球面上の結合・交換同型は順方向のhexagonを満たす。 -/
lemma sphereTensorHexagon_forward (E F G : SymmetricSpectrum.{u}) :
    (sphereTensorAssociator E F G).hom ≫ (sphereTensorSymmetry E (sphereTensor F G)).hom ≫
        (sphereTensorAssociator F G E).hom =
      sphereTensorMap (sphereTensorSymmetry E F).hom (𝟙 G) ≫
        (sphereTensorAssociator F E G).hom ≫ sphereTensorMap (𝟙 F) (sphereTensorSymmetry E G).hom :=
  MonoidalBalancedTensor.hexagon_forward sphereSequence.{u} E F G

/-- 球面上の結合・交換同型は逆方向のhexagonを満たす。 -/
lemma sphereTensorHexagon_reverse (E F G : SymmetricSpectrum.{u}) :
    (sphereTensorAssociator E F G).inv ≫ (sphereTensorSymmetry (sphereTensor E F) G).hom ≫
        (sphereTensorAssociator G E F).inv =
      sphereTensorMap (𝟙 E) (sphereTensorSymmetry F G).hom ≫
        (sphereTensorAssociator E G F).inv ≫ sphereTensorMap (sphereTensorSymmetry E G).hom (𝟙 F) :=
  MonoidalBalancedTensor.hexagon_reverse sphereSequence.{u} E F G

end SerrePositivity.SymmetricSpectrum
