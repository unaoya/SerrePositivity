module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.InternalHom
public import SerrePositivity.Spectra.General.TensorClosed
public import SerrePositivity.Spectra.SymmetricSpectrum.Sphere
public import SerrePositivity.Spectra.SymmetricSpectrum.Free
public import SerrePositivity.Spectra.SymmetricSpectrum.Evaluation

/-! # 円周を座標とするスペクトルの二変数内部 Hom -/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 原変数に反変な内部Homの二変数関手。 -/
abbrev internalHomBifunctor := MonoidalModuleInternalHom.homBifunctor sphereSequence.{u}

end SerrePositivity.SymmetricSpectrum
