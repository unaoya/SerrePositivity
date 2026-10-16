import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.NerveSimplexEndpoint

section GeneralIntervals
variable {D : Type uD} [Category.{vD} D] [ModelCategory SSet.{v}]
  (F : D ⥤ SSet.{v})
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hp : ∀ d, trivialFibrations SSet.{v} ((NerveCoherentExtension.projection F).app d))
  (p₀ p₁ : ∀ d, BoundaryOneCotensor.vertex ⟶ F.obj d)
  (edges : ∀ d, SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ F.obj d)
  (h₀ : ∀ d, SSet.stdSimplex.δ (1 : Fin 2) ≫ edges d = p₀ d)
  (h₁ : ∀ d, SSet.stdSimplex.δ (0 : Fin 2) ≫ edges d = p₁ d)

-- Two endpoint systems are fixed first. No coherent boundary or compatibility is supplied.
example (d : D) : NerveParameterExtension.evaluate F
    (NerveIntervalBoundary.betweenChosen F p₀ p₁ edges h₀ h₁ hcof hfib hp) d = edges d :=
  NerveIntervalBoundary.betweenChosen_evaluate _ _ _ _ _ _ _ _ _ d

example : NerveIntervalBoundary.betweenChosen F p₀ p₁ edges h₀ h₁ hcof hfib hp ≫
    NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F (SSet.stdSimplex.δ (1 : Fin 2))) =
    NerveIntervalBoundary.constant F BoundaryOneCotensor.vertex
      (NerveIntervalBoundary.chosenEndpoint F hcof hp p₀) :=
  NerveIntervalBoundary.betweenChosen_zero _ _ _ _ _ _ _ _ _

example : NerveIntervalBoundary.betweenChosen F p₀ p₁ edges h₀ h₁ hcof hfib hp ≫
    NerveRelativeValueExtension.valueMap _ _
      (NerveParameterExtension.restriction F (SSet.stdSimplex.δ (0 : Fin 2))) =
    NerveIntervalBoundary.constant F BoundaryOneCotensor.vertex
      (NerveIntervalBoundary.chosenEndpoint F hcof hp p₁) :=
  NerveIntervalBoundary.betweenChosen_one _ _ _ _ _ _ _ _ _

-- All external simplex operators act on the same interval system, including degeneracies.
example {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.stdSimplex.map θ ≫
      (NerveIntervalBoundary.betweenChosen F p₀ p₁ edges h₀ h₁ hcof hfib hp).app (ofChain c) =
    (NerveIntervalBoundary.betweenChosen F p₀ p₁ edges h₀ h₁ hcof hfib hp).app
      (ofChain ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) ≫
      (NerveParameterExtension.cotensor F _).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))) :=
  NerveCoherentFamily.reindex_compatibility _ _ c θ
end GeneralIntervals

section OldMixedIntervals
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (Y : FramedResolution C) (W : ResolutionObject C) (g : Y.inner.base ⟶ W.base)
open MixedChoiceCoherentIntervals

-- The actual four old intervals, with no supplied coherent boundary assumption.
example (e : Edge) (t : MixedChoiceFunctor.Context Y W) :
    NerveParameterExtension.evaluate (values hcof Y W g) (interval hcof hfib Y W g e) t =
      oldEdge hcof hfib Y W g e t := interval_evaluate _ _ _ _ _ e t

-- Original old points are retained by the four independently chosen whole endpoint systems.
example (j : Vertex) (t : MixedChoiceFunctor.Context Y W) :
    (endpoint hcof hfib Y W g j).app (ofChain (ComposableArrows.mk₀ t)) =
      point hcof Y W g j t := endpoint_point _ _ _ _ _ j t

-- The AB→BD junction is the same coherent B-system in every external degree.
example : interval hcof hfib Y W g .AB ≫
    NerveRelativeValueExtension.valueMap _ _ (NerveParameterExtension.restriction
      (values hcof Y W g) (SSet.stdSimplex.δ (0 : Fin 2))) =
    interval hcof hfib Y W g .BD ≫
    NerveRelativeValueExtension.valueMap _ _ (NerveParameterExtension.restriction
      (values hcof Y W g) (SSet.stdSimplex.δ (1 : Fin 2))) :=
  (interval_one _ _ _ _ _ .AB).trans (interval_zero _ _ _ _ _ .BD).symm

-- Both outgoing edges retain the same A-system, and both incoming edges the same D-system.
example : interval hcof hfib Y W g .AB ≫
    NerveRelativeValueExtension.valueMap _ _ (NerveParameterExtension.restriction
      (values hcof Y W g) (SSet.stdSimplex.δ (1 : Fin 2))) =
    interval hcof hfib Y W g .AC ≫
    NerveRelativeValueExtension.valueMap _ _ (NerveParameterExtension.restriction
      (values hcof Y W g) (SSet.stdSimplex.δ (1 : Fin 2))) :=
  (interval_zero _ _ _ _ _ .AB).trans (interval_zero _ _ _ _ _ .AC).symm

example : interval hcof hfib Y W g .BD ≫
    NerveRelativeValueExtension.valueMap _ _ (NerveParameterExtension.restriction
      (values hcof Y W g) (SSet.stdSimplex.δ (0 : Fin 2))) =
    interval hcof hfib Y W g .CD ≫
    NerveRelativeValueExtension.valueMap _ _ (NerveParameterExtension.restriction
      (values hcof Y W g) (SSet.stdSimplex.δ (0 : Fin 2))) :=
  (interval_one _ _ _ _ _ .BD).trans (interval_one _ _ _ _ _ .CD).symm
end OldMixedIntervals

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryOneCotensor,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveIntervalBoundary,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentIntervals]
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
    throwError "Some interval boundary modules were not audited"
  logInfo m!"Coherent interval boundary audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
