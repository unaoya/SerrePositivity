module

public import SerrePositivity.Spectra.General.Evaluation
public import SerrePositivity.Spectra.General.TensorClosed
public import SerrePositivity.Spectra.SymmetricSpectrum.Closed
public import SerrePositivity.Spectra.SymmetricSpectrum.Evaluation

/-! # Compatibility with the existing circle-based simplicial spectra

The old API is retained. These equalities check the actual chosen monoidal
and module structures, including the free/evaluation adjunction.
-/

@[expose] public section
universe u
noncomputable section
open CategoryTheory

namespace SerrePositivity.GeneralSymmetricSpectrum
open PointedSimplicialSet

lemma simplicial_type :
    GeneralSymmetricSpectrum PointedSimplicialSet.{u} circle = SymmetricSpectrum.{u} := rfl

lemma simplicial_forget :
    forget (circle : PointedSimplicialSet.{u}) = SymmetricSpectrum.forget.{u} := rfl

lemma simplicial_level (E : SymmetricSpectrum.{u}) (n : ℕ) :
    level (C := PointedSimplicialSet.{u}) (K := circle) E n = SymmetricSpectrum.level E n := rfl

lemma simplicial_action (E : SymmetricSpectrum.{u}) :
    action (C := PointedSimplicialSet.{u}) (K := circle) E = SymmetricSpectrum.action E := rfl

lemma simplicial_free :
    freeFunctor (circle : PointedSimplicialSet.{u}) = SymmetricSpectrum.freeFunctor.{u} := rfl

lemma simplicial_freeForgetAdjunction :
    freeForgetAdjunction (circle : PointedSimplicialSet.{u}) =
      SymmetricSpectrum.freeForgetAdjunction.{u} := rfl

lemma simplicial_evaluation (n : ℕ) :
    evaluation (K := (circle : PointedSimplicialSet.{u})) n =
      SymmetricSpectrum.evaluation.{u} n := rfl

lemma simplicial_freeAt (n : ℕ) :
    freeAt (K := (circle : PointedSimplicialSet.{u})) n = SymmetricSpectrum.freeAt.{u} n := rfl

lemma simplicial_freeAtAdjunction (n : ℕ) :
    freeAtAdjunction (K := (circle : PointedSimplicialSet.{u})) n =
      SymmetricSpectrum.freeAtAdjunction.{u} n := rfl
lemma simplicial_tensor (E F : SymmetricSpectrum.{u}) :
    tensor (C := PointedSimplicialSet.{u}) (K := circle) E F =
      SymmetricSpectrum.sphereTensor E F := rfl

lemma simplicial_internalHom (E F : SymmetricSpectrum.{u}) :
    internalHom (C := PointedSimplicialSet.{u}) (K := circle) E F =
      SymmetricSpectrum.internalHom E F := rfl

end SerrePositivity.GeneralSymmetricSpectrum
