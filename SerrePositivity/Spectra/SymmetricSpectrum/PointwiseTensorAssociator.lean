module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorFunctor
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorFreeAtSum
public import Mathlib.CategoryTheory.Whiskering
public import SerrePositivity.CategoryTheory.Monoidal.Action

/-! # 各段のsmashによる作用の結合比較 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 各段のsmashを持つテンソルの反復と入力のsmashの自然比較。 -/
abbrev pointwiseTensorAssociatorNatIso := GeneralSymmetricSpectrum.pointwiseTensorAssociatorNatIso (K := circle.{u})

end SerrePositivity.SymmetricSpectrum
