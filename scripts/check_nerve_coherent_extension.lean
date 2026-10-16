import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u w vD uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel

section InverseBoundary
variable (X : SSet.{w}) (s : X.Elementsᵒᵖ)
example [Nonempty (SimplexMatchingTerminal.Index X s)] :
    ∃ q : SimplexMatchingTerminal.Index X s, Nonempty (IsTerminal q) :=
  SimplexMatchingTerminal.exists_terminal X s
example (hs : s.unop.val ∈ X.nonDegenerate (SimplexMatchingTerminal.dimension X s)) :
    IsEmpty (SimplexMatchingTerminal.Index X s) :=
  SimplexMatchingTerminal.index_isEmpty_of_nonDegenerate X s hs
end InverseBoundary

section RelativeChoice
variable {D : Type uD} [Category.{vD} D] [ModelCategory SSet.{v}] (F : D ⥤ SSet.{v})
  (hp : ∀ d, trivialFibrations SSet.{v} ((NerveCoherentExtension.projection F).app d))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

-- Only the actual point projections are assumed trivial fibrations: no natural section is supplied.
example : Reedy.reedyRight (NerveCoherentFamily.reedy D) (trivialFibrations SSet.{v})
    (NerveCoherentExtension.valueProjection F) := NerveCoherentExtension.reedyRight F hp
example : Nonempty (NerveCoherentFamily.System F) :=
  NerveCoherentExtension.exists_system F hp hcof

variable {B : NerveSimplexEndpoint.Index D ⥤ SSet.{v}}
  (i : B ⟶ NerveCoherentFamily.simplices D)
  (hi : Reedy.reedyLeft (NerveCoherentFamily.reedy D) (cofibrations SSet.{v}) i)
  (a : B ⟶ NerveCoherentFamily.values F)
example : i ≫ NerveCoherentExtension.extend F hp i hi a = a :=
  NerveCoherentExtension.extend_initial F hp i hi a
example (s : NerveSimplexEndpoint.Index D) :
    i.app s ≫ (NerveCoherentExtension.extend F hp i hi a).app s = a.app s :=
  NerveCoherentExtension.extend_component F hp i hi a s

-- All external simplex operators use the same whole relative extension.
example {s t : NerveSimplexEndpoint.Index D} (f : s ⟶ t) :
    SSet.stdSimplex.map (NerveSimplexEndpoint.operator f) ≫
        (NerveCoherentExtension.extend F hp i hi a).app t =
      (NerveCoherentExtension.extend F hp i hi a).app s ≫
        F.map (NerveSimplexEndpoint.endpointMap f) :=
  NerveCoherentFamily.compatibility F (NerveCoherentExtension.extend F hp i hi a) f
end RelativeChoice

section ActualMixed
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (Y : HomotopyFunctionComplex.FramedResolution C) (W : HomotopyFunctionComplex.ResolutionObject C)
  (g : Y.inner.base ⟶ W.base)

-- The actual mixed comparison diagram is an instance, without restricting the model source.
example : Nonempty (NerveCoherentFamily.System
    (HomotopyFunctionComplex.MixedChoiceFunctor.functor Y W g hcof)) := by
  apply NerveCoherentExtension.exists_system _ ?_ hcof
  intro d
  have he : (NerveCoherentExtension.projection
      (HomotopyFunctionComplex.MixedChoiceFunctor.functor Y W g hcof)).app d =
      (HomotopyFunctionComplex.MixedChoiceFunctor.projection Y W g hcof).app d :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [he]
  exact HomotopyFunctionComplex.MixedChoiceFunctor.projection_trivialFibration Y W g hcof hfib d
end ActualMixed

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexMatchingTerminal,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexInverseMatching,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveCoherentExtension]
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
    throwError "Some mixed choice modules were not audited"
  logInfo m!"Coherent extension audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
