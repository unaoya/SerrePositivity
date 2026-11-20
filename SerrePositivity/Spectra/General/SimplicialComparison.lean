module

public import SerrePositivity.Spectra.General.Evaluation
public import SerrePositivity.Spectra.General.TensorClosed
public import SerrePositivity.Spectra.General.MappingObject
public import SerrePositivity.Spectra.General.StructureMaps
public import SerrePositivity.Spectra.General.FreeLevelQuotient
public import SerrePositivity.Spectra.SymmetricSpectrum.Sphere
public import SerrePositivity.Spectra.SymmetricSpectrum.Basic

/-! # Compatibility with the existing circle-based simplicial spectra

The comparison identifies the remaining tensor, internal Hom and enrichment constructions.
-/

@[expose] public section
universe u
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.GeneralSymmetricSpectrum
open PointedSimplicialSet

lemma simplicial_tensor (E F : SymmetricSpectrum.{u}) :
    tensor (C := PointedSimplicialSet.{u}) (K := circle) E F =
      E ⊗ F := rfl

lemma simplicial_internalHom (E F : SymmetricSpectrum.{u}) :
    internalHom (C := PointedSimplicialSet.{u}) (K := circle) E F =
      (ihom E).obj F := rfl

lemma simplicial_pointwiseTensor (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    pointwiseTensor (K := circle) X E = pointwiseTensor X E := rfl

lemma simplicial_cotensor (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    cotensor (K := circle) X E =
      MonoidalModuleInternalHom.transportedObj sphereSequence.{u}
        ((SymmetricSequence.freeAt 0).obj X) E (homBySequenceCotensorIso X E) := rfl

lemma simplicial_mappingObject (E F : SymmetricSpectrum.{u}) :
    mappingObject (K := (circle : PointedSimplicialSet.{u})) E F =
      (ihom E ⋙ SymmetricSpectrum.evaluation 0).obj F := rfl

lemma simplicial_pointwiseTensorAssociator (X Y : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) : pointwiseTensorAssociator (K := circle) X Y E =
      (SymmetricSpectrum.pointwiseTensorAssociatorNatIso X Y).app E := rfl

end SerrePositivity.GeneralSymmetricSpectrum
