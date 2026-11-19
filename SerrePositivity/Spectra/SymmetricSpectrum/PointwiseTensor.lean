module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSequence.PointwiseTensorModule
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorFreeZeroLevels

/-! # 各段が通常のsmashとなるテンソル・スペクトルとF_0との全体の比較 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (level)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 各段のsmashを持つテンソルの値域スペクトルに関する関手。 -/
abbrev pointwiseTensorFunctor := GeneralSymmetricSpectrum.pointwiseTensorFunctor (K := circle.{u})

/-- F_0 Xとの全体の比較は値域スペクトルに関する自然同型。 -/
abbrev sphereTensorFreeZeroPointwiseNatIso := GeneralSymmetricSpectrum.tensorFreeZeroPointwiseNatIso (K := circle.{u})

end SerrePositivity.SymmetricSpectrum
