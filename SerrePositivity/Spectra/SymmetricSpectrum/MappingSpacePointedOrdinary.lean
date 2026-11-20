module

public import SerrePositivity.Spectra.General.MappingEnrichment
public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpace

/-! # 基点付き豊穣構造と既存のスペクトルの圏構造の一致 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory

/-- 基点付き写像対象の豊穣構造を既存の通常の圏構造へ接続する。 -/
abbrev pointedMappingEnrichedOrdinaryCategory :=
  GeneralSymmetricSpectrum.mappingEnrichedOrdinaryCategory (K := PointedSimplicialSet.circle.{u})

end SerrePositivity.SymmetricSpectrum
