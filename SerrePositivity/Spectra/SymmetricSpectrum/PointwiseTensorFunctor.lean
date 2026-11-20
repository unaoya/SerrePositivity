module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensor

/-! # 各段のsmashを持つテンソルの二変数関手性 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 各段のsmashを持つテンソルは生成対象と値域スペクトルに共変な二変数関手。 -/
abbrev pointwiseTensorBifunctor := GeneralSymmetricSpectrum.pointwiseTensorBifunctor (K := circle.{u})

end SerrePositivity.SymmetricSpectrum
