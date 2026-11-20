module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.SimplicialTensorNaturality
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorUnit
public import SerrePositivity.Spectra.PointedSimplicialSet.AdjoinBasepointUnit
public import Mathlib.CategoryTheory.Adjunction.Unique
public import SerrePositivity.CategoryTheory.Adjunction.Comparison

/-! # 零次標準単体によるテンソルの単位比較 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory
open SerrePositivity.PointedSimplicialSet
open scoped Simplicial

/-- 零次標準単体によるtensorは恒等関手に自然に同型。 -/
def simplicialTensorUnitNatIso :
    simplicialTensorFunctor (Δ[0] : SSet.{u}) ≅ 𝟭 SymmetricSpectrum.{u} :=
  pointwiseTensorBifunctor.mapIso adjoinBasepointDeltaZeroIso ≪≫ pointwiseTensorUnitNatIso

end SerrePositivity.SymmetricSpectrum
