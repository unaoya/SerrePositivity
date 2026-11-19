module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.SimplicialTensorNaturality
public import SerrePositivity.Spectra.PointedSimplicialSet.AdjoinBasepointUnit
public import Mathlib.CategoryTheory.Adjunction.Unique
public import SerrePositivity.CategoryTheory.Adjunction.Comparison

/-! # 零次標準単体によるtensor・cotensorの単位比較 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory
open SerrePositivity.PointedSimplicialSet
open scoped Simplicial

/-- 零次標準単体によるtensorは恒等関手に自然に同型。 -/
def simplicialTensorUnitNatIso :
    simplicialTensorFunctor (Δ[0] : SSet.{u}) ≅ 𝟭 SymmetricSpectrum.{u} :=
  pointwiseTensorBifunctor.mapIso adjoinBasepointDeltaZeroIso ≪≫ pointwiseTensorUnitNatIso

/-- 零次標準単体によるcotensorは恒等関手に自然に同型。 -/
def simplicialCotensorUnitNatIso :
    simplicialCotensorFunctor (Δ[0] : SSet.{u}) ≅ 𝟭 SymmetricSpectrum.{u} :=
  ActionUnitAdjunction.rightUnitIso (simplicialTensorCotensorAdjunction (Δ[0] : SSet.{u}))
    simplicialTensorUnitNatIso

/-- 零次標準単体によるcotensorの単位同型。 -/
def simplicialCotensorUnitIso (E : SymmetricSpectrum.{u}) :
    simplicialCotensor (Δ[0] : SSet.{u}) E ≅ E := simplicialCotensorUnitNatIso.app E

/-- cotensorの単位比較はスペクトルの射に関して自然。 -/
lemma simplicialCotensorUnit_naturality {E F : SymmetricSpectrum.{u}} (f : E ⟶ F) :
    (simplicialCotensorFunctor (Δ[0] : SSet.{u})).map f ≫ (simplicialCotensorUnitIso F).hom =
      (simplicialCotensorUnitIso E).hom ≫ f := simplicialCotensorUnitNatIso.hom.naturality f

/-- cotensorの単位比較はtensorの逆単位比較と評価の合成。 -/
lemma simplicialCotensorUnitIso_hom (E : SymmetricSpectrum.{u}) :
    (simplicialCotensorUnitIso E).hom =
      (simplicialTensorUnitNatIso.app (simplicialCotensor (Δ[0] : SSet.{u}) E)).inv ≫
        (simplicialTensorCotensorAdjunction (Δ[0] : SSet.{u})).counit.app E :=
  ActionUnitAdjunction.rightUnitIso_hom
    (simplicialTensorCotensorAdjunction (Δ[0] : SSet.{u})) simplicialTensorUnitNatIso E

end SerrePositivity.SymmetricSpectrum
