import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarCompositionReindexLaws
import Lean.Util.CollectAxioms

universe u v
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed
open SerrePositivity SerrePositivity.SimplicialModel
open HomotopyFunctionComplex OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T U V : SSet.{v}} {X Y Z : D C}
  (j : UniverseLift.obj.{max u v} T ⟶ P)
  (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (g : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z)
  (c : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarRelativeHomDescent.choices hcof hfib P X Y)
  (d : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarRelativeHomDescent.choices hcof hfib P Y Z)
  (e : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarRelativeHomDescent.choices hcof hfib P X Z)

open OrdinaryBarRelativeHomDescent
-- Independent object/Hom universes, and strictly composing small reindexing maps.
example : compositionChoices_reindex hcof hfib P j f g c d e (𝟙 T) = 𝟙 _ :=
  compositionChoices_reindex_id hcof hfib P j f g c d e
example (i : U ⟶ T) (k : V ⟶ U) :
    compositionChoices_reindex hcof hfib P j f g c d e i ≫
      compositionChoices_reindex hcof hfib P (UniverseLift.map i ≫ j) (UniverseLift.map i ≫ f)
        (UniverseLift.map i ≫ g) (UniverseLift.map i ≫ c) (UniverseLift.map i ≫ d)
        (UniverseLift.map i ≫ e) k =
      compositionChoices_reindex hcof hfib P j f g c d e (k ≫ i) :=
  compositionChoices_reindex_comp hcof hfib P j f g c d e i k
example (i : U ⟶ T) {L : SSet.{v}} (q : L ⟶ compositionChoices hcof hfib P j f g c d e) :
    compositionChoiceFamily hcof hfib P (UniverseLift.map i ≫ j) (UniverseLift.map i ≫ f)
      (UniverseLift.map i ≫ g) (UniverseLift.map i ≫ c) (UniverseLift.map i ≫ d)
      (UniverseLift.map i ≫ e) (q ≫ compositionChoices_reindex hcof hfib P j f g c d e i) =
    i ▷ (SSet.stdSimplex.obj (SimplexCategory.mk 2) ⊗ L) ≫
      compositionChoiceFamily hcof hfib P j f g c d e q :=
  compositionChoiceFamily_reindex hcof hfib P j f g c d e i q
-- The actual relative comparison remains in the original small universe.
example (i : U ⟶ T) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⊗
      SSet.stdSimplex.obj (SimplexCategory.mk 1) ⟶
        (ihom U).obj ((ihom (small hcof hfib X)).obj (small hcof hfib Z)) :=
  (selectedTriangleReindexComparison hcof hfib P j f g c d e i).hom

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ComparisonTriangleTransport,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarCompositionReindex,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarCompositionReindexLaws]
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
  unless modules.size == expected.size do throwError "Missing triangle reindex modules"
  logInfo m!"Triangle reindex audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
