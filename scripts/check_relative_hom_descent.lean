import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison
import Lean.Util.CollectAxioms

universe u v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity SerrePositivity.SimplicialModel

-- No monomorphism assumption on a, and no value-side model structure.
example {A B K : SSet.{v}} (a : A ⟶ B)
    (ha : IsIso (AnodyneHomotopy.anodyneQ.map a))
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((pre a).app K)) :=
  KanRestrictionEquivalence.localized_isIso a ha hK
example {A B K U V : SSet.{v}} (a : A ⟶ B)
    (ha : IsIso (AnodyneHomotopy.anodyneQ.map a))
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) (h : A ⟶ K)
    (j : U ⟶ V) [Mono j] (c : U ⟶ RestrictionDescentChoices.obj a h) :
    ∃ e : V ⟶ RestrictionDescentChoices.obj a h,
      j ≫ e = c ∧ B ◁ j ≫ RestrictionDescentChoices.family a ha hK h e =
        RestrictionDescentChoices.family a ha hK h c ∧
      j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
        (RestrictionDescentChoices.parameterComparison a ha hK h e).h =
          (RestrictionDescentChoices.parameterComparison a ha hK h c).h :=
  RestrictionDescentChoices.relative_extension a ha hK h j c

open HomotopyFunctionComplex OrdinaryBarFreeResolutionSeed
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})
example (X Y : D C) : SSet.modelCategoryQuillen.I.rlp
    (terminal.from (OrdinaryBarRelativeHomDescent.choices hcof hfib P X Y)) :=
  OrdinaryBarRelativeHomDescent.choices_boundary_rlp hcof hfib P X Y
example {U V : SSet.{v}} {X Y : D C} (i : U ⟶ V) [Mono i]
    (j : UniverseLift.obj.{max u v} V ⟶ P)
    (f : UniverseLift.obj.{max u v} V ⟶ OrdinaryBarDiagonalHomAugmentation.baseHom C X Y)
    (c : UniverseLift.obj.{max u v} U ⟶
      OrdinaryBarRelativeHomDescent.choices hcof hfib P X Y) :
    ∃ e : UniverseLift.obj.{max u v} V ⟶
        OrdinaryBarRelativeHomDescent.choices hcof hfib P X Y,
      UniverseLift.map i ≫ e = c ∧ i ≫
        OrdinaryBarRelativeHomDescent.nativeFamily hcof hfib P j f e =
      OrdinaryBarRelativeHomDescent.nativeFamily hcof hfib P
        (UniverseLift.map i ≫ j) (UniverseLift.map i ≫ f) c :=
  OrdinaryBarRelativeHomDescent.native_relative_extension hcof hfib P i j f c

example {U V : SSet.{v}} {X Y : D C} (i : U ⟶ V) [Mono i]
    (j : UniverseLift.obj.{max u v} V ⟶ P)
    (g : UniverseLift.obj.{max u v} V ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
    (c : UniverseLift.obj.{max u v} U ⟶
      OrdinaryBarRelativeHomDescent.choices hcof hfib P X Y) :
    ∃ e : UniverseLift.obj.{max u v} V ⟶
        OrdinaryBarRelativeHomDescent.choices hcof hfib P X Y,
      UniverseLift.map i ≫ e = c ∧
        i ≫ OrdinaryBarRelativeHomDescent.nativeFamily hcof hfib P j
          (g ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y) e =
        OrdinaryBarRelativeHomDescent.nativeFamily hcof hfib P (UniverseLift.map i ≫ j)
          ((UniverseLift.map i ≫ g) ≫
            OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y) c ∧
        i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
          (OrdinaryBarRelativeHomDescent.nativeRestrictionComparison hcof hfib P j g e).h =
          (OrdinaryBarRelativeHomDescent.nativeRestrictionComparison hcof hfib P
            (UniverseLift.map i ≫ j) (UniverseLift.map i ≫ g) c).h :=
  OrdinaryBarRelativeHomDescent.native_relative_comparison_extension hcof hfib P i j g c

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RestrictionDescentEvaluation,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanPostDetection,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanRestrictionEquivalence,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.KanLocalizedComparisonResolution,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RestrictionDescentChoices,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent]
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
  unless modules.size == expected.size do throwError "Missing relative Hom descent modules"
  logInfo m!"Relative Hom descent audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
