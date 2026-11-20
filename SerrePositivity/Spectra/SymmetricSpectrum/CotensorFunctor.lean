module

public import SerrePositivity.Spectra.General.Cotensor
public import SerrePositivity.Spectra.SymmetricSpectrum.Sphere

/-! # 円周を座標とする余テンソル関手 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- cotensorの値域スペクトルに関する関手。 -/
abbrev cotensorFunctor := GeneralSymmetricSpectrum.cotensorFunctor (K := circle.{u})

end SerrePositivity.SymmetricSpectrum
