module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroUnit
public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroModuleUnit
public import SerrePositivity.Spectra.SymmetricSequence.PointwiseTensorModuleUnit
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorFunctor
public import SerrePositivity.Spectra.General.TensorFreeAtSum

/-! # 各段のsmashによる作用の単位比較 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 単位比較を値域スペクトルに関する自然同型へまとめる。 -/
abbrev pointwiseTensorUnitNatIso := GeneralSymmetricSpectrum.pointwiseTensorUnitNatIso (K := circle.{u})

end SerrePositivity.SymmetricSpectrum
