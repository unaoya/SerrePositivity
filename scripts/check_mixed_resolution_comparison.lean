import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u vH uH
noncomputable section
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.SimplicialModel
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- Both actual augmentation factors and their composite, at independent object/Hom universes.
example (X : ResolutionObject C) (Y : ResolutionObject Cᵒᵖ) :
    weakEquivalences SSet.{v} (MixedDiagonalHom.map
      (MixedResolutionComparison.augmentation X) (MixedResolutionComparison.augmentation Y)) :=
  MixedResolutionComparison.augmentation_weakEquivalence hcof hfib X Y

-- This is the same output used by the actual higher lift action, not a new value.
example (X : ResolutionObject C) (Y : ResolutionObject Cᵒᵖ) :
    MixedResolutionLiftAction.input X Y ⟶ MixedResolutionLiftAction.output X Y :=
  MixedDiagonalHom.map (MixedResolutionComparison.augmentation X)
    (MixedResolutionComparison.augmentation Y)

-- Strict lift actions are the actual Hom map followed by the proved comparison.
example {X X' : ResolutionObject C} (k : X ⟶ X')
    {Y Y' : ResolutionObject Cᵒᵖ} (l : Y ⟶ Y') {T : SSet.{v}}
    (d e : T ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (t : T ⟶ MixedResolutionLiftAction.input X' Y') :
    MixedResolutionLiftAction.action X X' k.base Y Y' l.base
        (d ≫ ResolutionLiftSpace.ofLift k) (e ≫ ResolutionLiftSpace.ofLift l) t =
      t ≫ MixedDiagonalHom.map k.diagram l.diagram ≫
        MixedDiagonalHom.map (MixedResolutionComparison.augmentation X)
          (MixedResolutionComparison.augmentation Y) :=
  MixedResolutionKanComparison.action_ofLift k l d e t

-- The common small Kan middle now maps naturally to all three actual Kan outputs.
example (X : RightResolutionMapping.Index C) :
    weakEquivalences SSet.{v} ((MixedResolutionKanComparison.comparison hcof hfib).app X) ∧
    weakEquivalences SSet.{v} ((BalancedResolutionComparison.left hcof hfib).app X) ∧
    weakEquivalences SSet.{v} ((BalancedResolutionComparison.right hcof hfib).app X) :=
  ⟨MixedResolutionKanComparison.comparison_weakEquivalence hcof hfib X,
    BalancedResolutionComparison.left_weakEquivalence hcof hfib X,
    BalancedResolutionComparison.right_weakEquivalence hcof hfib X⟩

example {X Y : RightResolutionMapping.Index C} (f : X ⟶ Y)
    (hs : weakEquivalences C f.1.unop.map.base)
    (ht : weakEquivalences C ((RightResolutionMapping.projection (C := C)).map f).2) :
    weakEquivalences SSet.{v} ((MixedResolutionKanComparison.functor hcof hfib).map f) :=
  MixedResolutionKanComparison.map_weakEquivalence hcof hfib f hs ht

example {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
    [Q.IsLocalization (weakEquivalences C)] (X : RightResolutionMapping.Index C) :
    SSet.π₀ ((MixedResolutionKanComparison.functor hcof hfib).obj X) ≃
      (Q.obj ((RightResolutionMapping.projection (C := C)).obj X).1.unop ⟶
        Q.obj ((RightResolutionMapping.projection (C := C)).obj X).2) :=
  MixedResolutionKanComparison.piZeroEquiv hcof hfib Q X

-- Full center transport is retained in the same diagram as the previous chain action.
example {q p : MixedResolutionCenters.Index C} (f : q ⟶ p) :
    ((MixedCenterComparison.sources C ⋙ BalancedResolutionComparison.middle hcof hfib).map f) ≫
        (MixedCenterComparison.kanComparison C hcof hfib).app p =
      (MixedCenterComparison.kanComparison C hcof hfib).app q ≫
        (MixedResolutionCenters.kanOutput C hcof hfib).map f :=
  (MixedCenterComparison.kanComparison C hcof hfib).naturality f

example (q : MixedResolutionCenters.Index C) :
    weakEquivalences SSet.{v} ((MixedCenterComparison.kanComparison C hcof hfib).app q) :=
  MixedCenterComparison.kanComparison_weakEquivalence C hcof hfib q

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedDiagonalRows,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedResolutionComparison,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedResolutionKanComparison,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedCenterComparison]
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
    throwError "Some mixed resolution comparison modules were not audited"
  logInfo m!"Mixed resolution comparison audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
