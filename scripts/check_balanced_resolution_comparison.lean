import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u uH vH
noncomputable section
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C]

-- The raw coordinate swap is an actual natural isomorphism, before any value model.
example : BiresolutionRawMapping.functor (C := C) ≅ BiresolutionRightMapping.rawFunctor :=
  BiresolutionRightMapping.rawFlipIso
example (X : RightResolutionMapping.Index C) (n : SimplexCategoryᵒᵖ)
    (f : ((BiresolutionRawMapping.functor (C := C)).obj X).obj n) :
    BiresolutionRightMapping.rawSimplexEquiv X n f = f.op := rfl

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
example : RightResolutionMapping.Index C ⥤ SSet.{v} :=
  BalancedResolutionComparison.rightFunctor hcof hfib
example (X : RightResolutionMapping.Index C) :
    weakEquivalences SSet.{v} ((BalancedResolutionComparison.left hcof hfib).app X) ∧
      weakEquivalences SSet.{v} ((BalancedResolutionComparison.right hcof hfib).app X) :=
  ⟨BalancedResolutionComparison.left_weakEquivalence hcof hfib X,
    BalancedResolutionComparison.right_weakEquivalence hcof hfib X⟩
example (X : RightResolutionMapping.Index C) :
    SSet.KanComplex ((BalancedResolutionComparison.middle hcof hfib).obj X) ∧
      SSet.KanComplex ((BalancedResolutionComparison.rightFunctor hcof hfib).obj X) :=
  ⟨BalancedResolutionComparison.middle_kanComplex hcof hfib X,
    BalancedResolutionComparison.right_kanComplex hcof hfib X⟩
example {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
    [Q.IsLocalization (weakEquivalences C)] (X : RightResolutionMapping.Index C) :
    SSet.π₀ ((BalancedResolutionComparison.rightFunctor hcof hfib).obj X) ≃
      (Q.obj ((RightResolutionMapping.projection (C := C)).obj X).1.unop ⟶
        Q.obj ((RightResolutionMapping.projection (C := C)).obj X).2) :=
  BalancedResolutionComparison.rightPiZeroEquiv hcof hfib Q X
example {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
    [L.IsLocalization (weakEquivalences SSet.{v})] :
    RightResolutionMapping.kanFunctor (C := C) hcof hfib ⋙ L ≅
      BalancedResolutionComparison.rightFunctor hcof hfib ⋙ L :=
  BalancedResolutionComparison.localizedIso hcof hfib L

section ActualRightLiftAction
open BiresolutionRightAction
variable (q : Centers C) (A : (FramedResolution C)ᵒᵖ)
example : SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.BoundaryFillers ((choices C).obj q) :=
  choice_fillers C hcof q
example : (coherent C hcof).app
    (SerrePositivity.NerveSimplexEndpoint.ofChain (ComposableArrows.mk₀ q)) =
      ResolutionArrowDiagram.selectedPoint Cᵒᵖ q := coherent_point C hcof q
example {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) {T : SSet.{v}}
    (s : T ⟶ (choices C).obj q)
    (t : T ⟶ (BiresolutionRightMapping.rawRows.obj n).obj (inputPair C q A)) :
    action C hcof hfib q A m s
        (t ≫ (BiresolutionRightMapping.rawRows.map θ).app (inputPair C q A)) =
      action C hcof hfib q A n s t ≫
        ((BiresolutionRightMapping.rows hcof hfib).map θ).app (outputPair C q A) :=
  action_source_operator C hcof hfib q A θ s t
example {r : Centers C} (f : q ⟶ r) (m : SimplexCategoryᵒᵖ) {T : SSet.{v}}
    (s : T ⟶ (choices C).obj q)
    (t : T ⟶ (BiresolutionRightMapping.rawRows.obj m).obj (inputPair C r A)) :
    action C hcof hfib r A m (s ≫ (choices C).map f) t =
      action C hcof hfib q A m s
          (t ≫ (ResolutionArrowActionFunctors.input Cᵒᵖ (sourcePoint C A m)).map f.op) ≫
        (ResolutionArrowActionFunctors.output Cᵒᵖ hcof hfib (sourcePoint C A m)).map f :=
  action_center C hcof hfib f A m s t
end ActualRightLiftAction

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.BiresolutionRawMapping,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.BiresolutionRightMapping,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.BalancedResolutionComparison,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.BiresolutionRightAction]
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
    throwError "Some balanced resolution comparison modules were not audited"
  logInfo m!"Balanced resolution comparison audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
