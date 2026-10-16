import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w uD vD v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open HomotopicalAlgebra SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open NerveCylinderBoundary NerveBiparameterMaps

section GeneralMovingBoundary
-- Neither a model structure nor equality of index object and Hom universes is required.
variable {D : Type uD} [Category.{vD} D] (K F : D ⥤ SSet.{w}) {n : ℕ}
  (faces : Fin (n + 3) → NerveBiparameter.System
    (product K (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))) F)
  (hf : NerveMovingBoundary.Compatible K F faces)
example (k : Fin (n + 3)) : NerveMovingBoundary.boundary K F faces hf ≫ restriction _ _ F
    (vertical (SSet.boundary.ι k) K) = faces k :=
  NerveMovingBoundary.boundary_face K F faces hf k
example {a b : NerveBiparameter.System (product K (SSet.boundary (n + 1)).toSSet) F}
    (h : ∀ k : Fin (n + 2), a ≫ restriction _ _ F (vertical (SSet.boundary.ι k) K) =
      b ≫ restriction _ _ F (vertical (SSet.boundary.ι k) K)) : a = b :=
  NerveMovingBoundary.hom_ext K F h
end GeneralMovingBoundary

section ActualMixedBoundary
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
open ResolutionMixedDiagram ResolutionMixedBoundary
-- The fixed facet systems are retained as whole systems in all external degrees.
example (side : Bool) (k : Fin 3) : system C hcof hfib side ≫
    restriction _ _ (NerveMovingParameter.lifted (smallValues C)) (faceInclusion C k) =
    ResolutionMixedFaceSystems.faces C hcof hfib side k := system_face C hcof hfib side k
example : system C hcof hfib true ≫
    restriction _ _ (NerveMovingParameter.lifted (smallValues C)) (faceInclusion C 1) =
    system C hcof hfib false ≫
      restriction _ _ (NerveMovingParameter.lifted (smallValues C)) (faceInclusion C 1) :=
  shared_diagonal C hcof hfib
-- Each already chosen entire triangle fits the actual glued boundary.
example (side : Bool) (p : Index C) : (inclusion C).app p ≫
    ResolutionMixedTriangles.triangle C hcof hfib p side =
    NerveMovingParameter.evaluate (boundaryParameter C) (smallValues C)
      (system C hcof hfib side) p := triangle_fit C hcof hfib side p
end ActualMixedBoundary

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.ProductBoundaryCotensor,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveMovingBoundary,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedBoundary]
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
    throwError "Some moving mixed boundary modules were not audited"
  logInfo m!"Moving mixed boundary audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
