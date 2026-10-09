module

public import SerrePositivity.CommutativeAlgebra.LengthComparison
public import SerrePositivity.IntersectionMultiplicity.TwistEvaluation
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Ordinary lengths over local coefficient rings

If the residue map of a local algebra is surjective from the base, every
simple coefficient module has base length one. Composition-series induction
then identifies the two ordinary lengths.
-/

public section

universe u

open IsLocalRing
open CategoryTheory

namespace SerrePositivity

variable {R T : Type u} [CommRing R] [IsLocalRing R] [CommRing T] [IsLocalRing T]
  [Algebra R T]

omit [IsLocalRing R] [IsLocalRing T] in
/-- Finite length after restricting scalars implies finite length over the
coefficient ring: its submodule lattice embeds into the base submodule lattice. -/
lemma finiteLength_of_restrictScalars (M : ModuleCat.{u} T)
    (hM : IsFiniteLength R ((ModuleCat.restrictScalars (algebraMap R T)).obj M)) :
    IsFiniteLength T M := by
  let : Module R M := Module.compHom M (algebraMap R T)
  have : IsScalarTower R T M := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  have h : IsFiniteLength R M := hM
  obtain ⟨hn, ha⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_of_tower R hn, isArtinian_of_tower R ha⟩

omit [IsLocalRing R] in
/-- The same length comparison expressed using the restriction functor. -/
lemma length_restrictScalars_eq_of_residue_surjective
    (hres : Function.Surjective ((residue T).comp (algebraMap R T)))
    (M : ModuleCat.{u} T) (_hM : IsFiniteLength T M) :
    Module.length R ((ModuleCat.restrictScalars (algebraMap R T)).obj M) = Module.length T M := by
  exact length_restrictScalars_eq hres M

end SerrePositivity
