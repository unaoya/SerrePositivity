module

public import SerrePositivity.Spectra.General.Evaluation
public import SerrePositivity.Spectra.General.TensorClosed
public import SerrePositivity.Spectra.General.MappingObject
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorAdjunction
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorAssociatorLevels
public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpace
public import SerrePositivity.Spectra.General.StructureMaps
public import SerrePositivity.Spectra.General.FreeLevelQuotient
public import SerrePositivity.Spectra.SymmetricSpectrum.StructureMaps
public import SerrePositivity.Spectra.SymmetricSpectrum.FreeLevelQuotient
public import SerrePositivity.Spectra.SymmetricSpectrum.Closed
public import SerrePositivity.Spectra.SymmetricSpectrum.Evaluation

/-! # Compatibility with the existing circle-based simplicial spectra

The comparison identifies the remaining tensor, internal Hom and enrichment constructions.
-/

@[expose] public section
universe u
noncomputable section
open CategoryTheory

namespace SerrePositivity.GeneralSymmetricSpectrum
open PointedSimplicialSet

lemma simplicial_tensor (E F : SymmetricSpectrum.{u}) :
    tensor (C := PointedSimplicialSet.{u}) (K := circle) E F =
      SymmetricSpectrum.sphereTensor E F := rfl

lemma simplicial_internalHom (E F : SymmetricSpectrum.{u}) :
    internalHom (C := PointedSimplicialSet.{u}) (K := circle) E F =
      SymmetricSpectrum.internalHom E F := rfl

lemma simplicial_pointwiseTensor (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    pointwiseTensor (K := circle) X E = SymmetricSpectrum.pointwiseTensor X E := rfl

lemma simplicial_cotensor (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    cotensor (K := circle) X E = SymmetricSpectrum.cotensor X E := rfl

lemma simplicial_mappingObject (E F : SymmetricSpectrum.{u}) :
    mappingObject (K := (circle : PointedSimplicialSet.{u})) E F =
      SymmetricSpectrum.pointedMappingSpace E F := rfl

lemma simplicial_pointwiseTensorAssociator (X Y : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) : pointwiseTensorAssociator (K := circle) X Y E =
      SymmetricSpectrum.pointwiseTensorAssociator X Y E := by
  apply CategoryTheory.Iso.ext
  exact (SymmetricSpectrum.pointwiseTensorAssociator_module_hom X Y E).symm

end SerrePositivity.GeneralSymmetricSpectrum
