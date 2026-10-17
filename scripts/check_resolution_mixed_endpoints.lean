import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe w uD vD uE vE v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

section ExactWholeTransport
-- Pure whole-system laws; no model structure or equality between object and Hom universes.
variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  (K F : D ⥤ SSet.{w}) (a : NerveBiparameter.System K F)
  (H J L : E ⥤ D) (τ : H ⟶ J) (σ : J ⟶ L)
open NerveArrowComparisonComposition NerveBiparameterMaps

example : mapTarget _ _ _ (Functor.whiskerRight σ F) (leftAlong K F a H J τ) =
    leftAlong K F a H L (τ ≫ σ) := left_follow K F a H J L τ σ

example : mapTarget _ _ _ (Functor.whiskerRight σ F) (rightAlong K F a H J τ) =
    restrict _ _ _ (Functor.whiskerRight τ K) (leftAlong K F a J L σ) :=
  middle_exchange K F a H J L τ σ

example (h : J = L) : mapTarget _ _ _ (Functor.whiskerRight (eqToHom h) F)
    (rightAlong K F a H J τ) = rightAlong K F a H L (τ ≫ eqToHom h) :=
  right_follow_eq K F a H J L τ h
end ExactWholeTransport

section AllFourWholeCorners
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
open ResolutionMixedDiagram ResolutionMixedReassociation ResolutionMixedReassociationEquality
open ResolutionMixedIntervalRestrictions ResolutionMixedEndpointCompatibility

-- The reassociation really is equality transport of the same entire indexing functor.
example : toFinal C = eqToIso (finalLeft_eq C) := toFinal_eq C

-- All four identities are identities of whole systems, including every external face/degeneracy.
example : endpoint C (intervalAB C hcof hfib) 1 = endpoint C (intervalAC C hcof hfib) 1 :=
  commonA C hcof hfib
example : endpoint C (intervalAB C hcof hfib) 0 = endpoint C (intervalBD C hcof hfib) 1 :=
  commonB C hcof hfib
example : endpoint C (intervalAC C hcof hfib) 0 = endpoint C (intervalCD C hcof hfib) 1 :=
  commonC C hcof hfib
example : endpoint C (intervalBD C hcof hfib) 0 = endpoint C (intervalCD C hcof hfib) 0 :=
  commonD C hcof hfib

-- Both final facets are the same full corner3 system from the original all-center tuple system.
example : endpoint C (intervalBD C hcof hfib) 0 = expand C (corner3 C hcof) :=
  BD_one C hcof hfib
example : endpoint C (intervalCD C hcof hfib) 0 = expand C (corner3 C hcof) :=
  CD_one C hcof hfib
end AllFourWholeCorners

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
  `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveBiparameterComposition,
  `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveArrowComparisonComposition,
  `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveProductEndpointTransport,
  `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.SelectedIntervalEndpoints,
  `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedReassociationEquality,
  `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedRawEndpoints,
  `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedEndpointCompatibility]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  unless modules.size == expected.size do
    throwError "Some whole mixed endpoint modules were not audited"
  logInfo m!"Whole mixed endpoint audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
