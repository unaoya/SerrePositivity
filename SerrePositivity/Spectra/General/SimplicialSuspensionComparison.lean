module

public import SerrePositivity.Spectra.General.SimplicialComparison
public import SerrePositivity.Spectra.General.Suspension
public import SerrePositivity.Spectra.SymmetricSpectrum.SuspensionLoop
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

lemma simplicial_pointwiseTensorFunctor (X : PointedSimplicialSet.{u}) :
    pointwiseTensorFunctor (K := circle) X = SymmetricSpectrum.pointwiseTensorFunctor X := rfl

def simplicialCotensorNatIso (X : PointedSimplicialSet.{u}) :
    cotensorFunctor (K := (circle : PointedSimplicialSet.{u})) X ≅
      SymmetricSpectrum.cotensorFunctor.{u} X :=
  Adjunction.rightAdjointUniq
    (pointwiseTensorCotensorAdjunction (K := (circle : PointedSimplicialSet.{u})) X)
    (SymmetricSpectrum.pointwiseTensorCotensorAdjunction.{u} X)

lemma simplicial_suspensionFunctor :
    pointwiseTensorFunctor (K := (circle : PointedSimplicialSet.{u})) circle =
      SymmetricSpectrum.suspensionFunctor := rfl

def simplicialLoopNatIso :
    cotensorFunctor (K := (circle : PointedSimplicialSet.{u})) circle ≅
      cotensorFunctor (K := circle.{u}) circle :=
  Adjunction.rightAdjointUniq
    (pointwiseTensorCotensorAdjunction (K := (circle : PointedSimplicialSet.{u})) circle)
    SymmetricSpectrum.suspensionLoopAdjunction.{u}

lemma simplicial_suspensionLoopUnit (E : SymmetricSpectrum.{u}) :
    (pointwiseTensorCotensorAdjunction
      (K := (circle : PointedSimplicialSet.{u})) circle).unit.app E ≫
      simplicialLoopNatIso.hom.app (SymmetricSpectrum.suspensionFunctor.obj E) =
        SymmetricSpectrum.suspensionLoopAdjunction.unit.app E := by
  simpa only [simplicialLoopNatIso] using
    Adjunction.unit_rightAdjointUniq_hom_app
    (pointwiseTensorCotensorAdjunction (K := (circle : PointedSimplicialSet.{u})) circle)
    SymmetricSpectrum.suspensionLoopAdjunction.{u} E

lemma simplicial_suspensionLoopCounit (E : SymmetricSpectrum.{u}) :
    SymmetricSpectrum.suspensionFunctor.map (simplicialLoopNatIso.hom.app E) ≫
      SymmetricSpectrum.suspensionLoopAdjunction.counit.app E =
        (pointwiseTensorCotensorAdjunction
          (K := (circle : PointedSimplicialSet.{u})) circle).counit.app E := by
  simpa only [simplicialLoopNatIso] using
    Adjunction.rightAdjointUniq_hom_app_counit
    (pointwiseTensorCotensorAdjunction (K := (circle : PointedSimplicialSet.{u})) circle)
    SymmetricSpectrum.suspensionLoopAdjunction.{u} E

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
