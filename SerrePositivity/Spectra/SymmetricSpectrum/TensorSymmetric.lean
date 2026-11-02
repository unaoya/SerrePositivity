module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.Symmetric
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorMonoidal
public import SerrePositivity.Spectra.SymmetricSpectrum.TensorHexagon

/-! # 球面上の対称スペクトルの対称モノイダル構造 -/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 球面上の釣り合いテンソル積と交換による対称モノイダル構造。 -/
instance sphereTensorSymmetricCategory : SymmetricCategory SymmetricSpectrum.{u} :=
  MonoidalBalancedTensor.symmetricCategory sphereSequence.{u}

/-- 登録したスペクトルのbraidingは構成済みの交換同型。 -/
lemma braiding_eq_sphereTensorSymmetry (E F : SymmetricSpectrum.{u}) :
    β_ E F = sphereTensorSymmetry E F := rfl

end SerrePositivity.SymmetricSpectrum
