import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v uD vD u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

section FromObjectwiseEquations
-- Independent indexing universes, small values, and no model in the larger universe.
variable {D : Type uD} [Category.{vD} D]
  (L K : D ⥤ SSet.{max w v}) (i : L ⟶ K) (F : D ⥤ SSet.{v})
  (target : NerveMovingParameter.System L F)
  (families : ∀ d, K.obj d ⟶ UniverseLift.obj.{w} (F.obj d))
  (he : ∀ d, i.app d ≫ families d = NerveMovingParameter.evaluate L F target d)
  (hp : ∀ d, UniverseLift.BoundaryFillers (F.obj d)) (hi : ∀ d, Mono (i.app d))

-- No supplied lower-system compatibility or naturally varying original families.
example (d : D) : NerveMovingParameter.evaluate K F
    (NerveMovingFamilyFit.extend K F L i families target he hp hi) d = families d :=
  NerveMovingFamilyFit.extend_evaluate _ _ _ _ _ _ _ _ _ d

example : NerveMovingFamilyFit.extend K F L i families target he hp hi ≫
    NerveMovingParameterRelative.restriction L K i F = target :=
  NerveMovingFamilyFit.extend_boundary _ _ _ _ _ _ _ _ _
end FromObjectwiseEquations

section ActualThreeBoundaryEquations
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (d : ResolutionArrowCylinderFamilyFit.Data C hcof)
open ResolutionArrowComparisonEndpoints ResolutionArrowCylinderBoundary
open ResolutionArrowCylinderFamilyFit

-- Three actual restrictions imply the single whole-Q equation; no extra fit assumption.
example (e : Arrow (ResolutionArrowDiagram.Index C)) : (inclusion C).app e ≫ d.family e =
    NerveMovingParameter.evaluate (boundaryParameter C) (values C) (system C hcof) e :=
  family_fit C hcof d e

-- Every entire original interval family is recovered as the actual large auxiliary map.
example (e : Arrow (ResolutionArrowDiagram.Index C)) :
    NerveMovingParameter.evaluate (fullParameter C) (values C) (extendFamilies C hcof d) e =
      d.family e := extendFamilies_evaluate C hcof d e

example : extendFamilies C hcof d ≫ NerveMovingParameterRelative.restriction
    (boundaryParameter C) (fullParameter C) (inclusion C) (values C) = system C hcof :=
  extendFamilies_boundary C hcof d

-- The same original whole endpoint system stays fixed throughout all external degrees.
example : extendFamilies C hcof d ≫ NerveBiparameterMaps.restriction _ _
    (NerveMovingParameter.lifted (values C)) (zeroInclusion C ≫ inclusion C) =
      NerveProductParameter.expand _ _ _ (left C hcof) := by
  rw [← NerveBiparameterMaps.restriction_comp, ← Category.assoc]
  exact (congrArg (fun a => a ≫ NerveBiparameterMaps.restriction _ _
    (NerveMovingParameter.lifted (values C)) (zeroInclusion C))
      (extendFamilies_boundary C hcof d)).trans (system_zero C hcof)
end ActualThreeBoundaryEquations

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveMovingFamilyFit,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveEvaluationLaws,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderFamilyFit]
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
    throwError "Some actual whole family fit modules were not audited"
  logInfo m!"Actual whole family fit audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
