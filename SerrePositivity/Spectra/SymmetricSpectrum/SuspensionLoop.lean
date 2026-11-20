module

public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorAdjunction

/-! # 円によるスペクトルの懸垂・ループの随伴 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (level)

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.PointedSimplicialSet

/-- 円の各段のsmashによる懸垂関手。 -/
abbrev suspensionFunctor :=
  GeneralSymmetricSpectrum.pointwiseTensorFunctor (K := circle.{u}) circle

/-- 懸垂とループの随伴。 -/
abbrev suspensionLoopAdjunction :=
  GeneralSymmetricSpectrum.pointwiseTensorCotensorAdjunction (K := circle.{u}) circle

end SerrePositivity.SymmetricSpectrum
