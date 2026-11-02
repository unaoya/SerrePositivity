module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.Monoidal
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorAssociator

/-! # 球面上のテンソル積のpentagon整合性 -/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 左結合した四重テンソル積への四因子からの標準射。 -/
def tensorQuadrupleLeftProjection (E F G H : SymmetricSpectrum.{u}) :
    ((E.X ⊗ F.X) ⊗ G.X) ⊗ H.X ⟶ (sphereTensor (sphereTensor (sphereTensor E F) G) H).X :=
  MonoidalBalancedTensor.quadrupleLeftProjection sphereSequence.{u} E F G H

/-- 四因子の標準射はエピ射。 -/
instance tensorQuadrupleLeftProjection_epi (E F G H : SymmetricSpectrum.{u}) :
    Epi (tensorQuadrupleLeftProjection E F G H) :=
  MonoidalBalancedTensor.quadrupleLeftProjection_epi sphereSequence.{u} E F G H

/-- 球面上のテンソル積の結合同型はpentagon整合性を満たす。 -/
lemma sphereTensorPentagon (E F G H : SymmetricSpectrum.{u}) :
    sphereTensorMap (sphereTensorAssociator E F G).hom (𝟙 H) ≫
        (sphereTensorAssociator E (sphereTensor F G) H).hom ≫
          sphereTensorMap (𝟙 E) (sphereTensorAssociator F G H).hom =
      (sphereTensorAssociator (sphereTensor E F) G H).hom ≫
        (sphereTensorAssociator E F (sphereTensor G H)).hom :=
  MonoidalBalancedTensor.pentagon sphereSequence.{u} E F G H

end SerrePositivity.SymmetricSpectrum
