module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorFunctor
public import SerrePositivity.Spectra.SymmetricSpectrum.CotensorFunctor

/-! # 各段のsmashを持つテンソルとcotensorの随伴 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (pointwiseTensor)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 各段の通常のsmashを持つテンソルはcotensor関手の左随伴。 -/
abbrev pointwiseTensorCotensorAdjunction :=
  GeneralSymmetricSpectrum.pointwiseTensorCotensorAdjunction (K := circle.{u})

end SerrePositivity.SymmetricSpectrum
