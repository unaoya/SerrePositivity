module

public import SerrePositivity.Spectra.General.SimplicialComparison
public import SerrePositivity.Spectra.General.Suspension
public import SerrePositivity.Spectra.SymmetricSpectrum.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Actual suspension, loop and bonding-map compatibility for circle spectra

These compare the chosen functors, adjunction and its structural maps, not
only their objects or levels. They do not assert homotopy-pushout stability.
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.GeneralSymmetricSpectrum
open PointedSimplicialSet

def simplicialCotensorNatIso (X : PointedSimplicialSet.{u}) :
    cotensorFunctor (K := (circle : PointedSimplicialSet.{u})) X ≅
      SymmetricSpectrum.cotensorFunctor.{u} X :=
  Adjunction.rightAdjointUniq
    (pointwiseTensorCotensorAdjunction (K := (circle : PointedSimplicialSet.{u})) X)
    (SymmetricSpectrum.pointwiseTensorCotensorAdjunction.{u} X)

def simplicialLoopNatIso :
    cotensorFunctor (K := (circle : PointedSimplicialSet.{u})) circle ≅
      SymmetricSpectrum.loopFunctor.{u} :=
  Adjunction.rightAdjointUniq
    (pointwiseTensorCotensorAdjunction (K := (circle : PointedSimplicialSet.{u})) circle)
    SymmetricSpectrum.suspensionLoopAdjunction.{u}

lemma simplicial_suspensionMap (E : SymmetricSpectrum.{u}) (n : ℕ) :
    suspensionMap (K := circle) E n =
      PointedObject.smashMap spherePowerOneIso.{u}.inv (𝟙 (level E n)) ≫
        structureMap E 1 n ≫ eqToHom (congrArg (level E) (Nat.one_add n)) := rfl

lemma simplicial_adjointStructureMap (E : SymmetricSpectrum.{u}) (n : ℕ) :
    adjointStructureMap (K := circle) E n =
      MonoidalClosed.curry
        (PointedObject.smashMap spherePowerOneIso.{u}.inv (𝟙 (level E n)) ≫
          structureMap E 1 n ≫ eqToHom (congrArg (level E) (Nat.one_add n))) := by
  rw [adjointStructureMap, simplicial_suspensionMap]

end SerrePositivity.GeneralSymmetricSpectrum
