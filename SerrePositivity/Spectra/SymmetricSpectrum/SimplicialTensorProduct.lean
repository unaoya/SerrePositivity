module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.SimplicialTensorUnit
public import SerrePositivity.Spectra.PointedSimplicialSet.AdjoinBasepointProduct
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorAssociator
public import SerrePositivity.CategoryTheory.Adjunction.Comparison

/-!
# 直積による反復テンソルの比較

自由基点追加の直積比較と各段のsmashの結合同型から、直積によるtensorを反復作用へ移す。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 直積によるtensorは、第二因子のtensor、第一因子のtensorの順の反復に自然に同型。 -/
def simplicialTensorProductNatIso (K L : SSet.{u}) :
    simplicialTensorFunctor (K ⊗ L) ≅ simplicialTensorFunctor L ⋙ simplicialTensorFunctor K :=
  pointwiseTensorBifunctor.mapIso (adjoinBasepointProductIso K L).symm ≪≫
    pointwiseTensorAssociatorNatIso (adjoinBasepoint K) (adjoinBasepoint L)

end SerrePositivity.SymmetricSpectrum
