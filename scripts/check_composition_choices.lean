import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarCompositionChoices
import Lean.Util.CollectAxioms

universe u v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity SerrePositivity.SimplicialModel

-- Every triangle and every parameter boundary is in the original universe.
example {T K : SSet.{v}} {f g z : T ⟶ K}
    (F : SSet.Homotopy f z) (G : SSet.Homotopy g z)
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) :
    SSet.modelCategoryQuillen.I.rlp (terminal.from (ComparisonTriangleChoices.obj F G)) :=
  ComparisonTriangleChoices.boundary_rlp F G hK
example {T K : SSet.{v}} {f g z : T ⟶ K}
    (F : SSet.Homotopy f z) (G : SSet.Homotopy g z)
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))
    (a b : KanComparisonTriangle.Data F G) :
    RelativeChoiceSpace.FixedBoundaryHomotopy (SSet.horn 2 2).ι
      (KanComparisonTriangle.hornMap F G) a.triangle b.triangle :=
  ComparisonTriangleChoices.fixedBoundaryComparison F G hK a b

open HomotopyFunctionComplex OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T : SSet.{v}} {X Y Z : D C}
  (j : UniverseLift.obj.{max u v} T ⟶ P)
  (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (g : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z)
  (c : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarRelativeHomDescent.choices hcof hfib P X Y)
  (d : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarRelativeHomDescent.choices hcof hfib P Y Z)
  (e : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarRelativeHomDescent.choices hcof hfib P X Z)

example : SSet.{v} := OrdinaryBarRelativeHomDescent.compositionChoices hcof hfib P j f g c d e
example {U V : SSet.{v}} (i : U ⟶ V) [Mono i]
    (q : U ⟶ OrdinaryBarRelativeHomDescent.compositionChoices hcof hfib P j f g c d e) :
    ∃ r : V ⟶ OrdinaryBarRelativeHomDescent.compositionChoices hcof hfib P j f g c d e,
      i ≫ r = q ∧ T ◁ (SSet.stdSimplex.obj (SimplexCategory.mk 2) ◁ i) ≫
        OrdinaryBarRelativeHomDescent.compositionChoiceFamily hcof hfib P j f g c d e r =
        OrdinaryBarRelativeHomDescent.compositionChoiceFamily hcof hfib P j f g c d e q :=
  OrdinaryBarRelativeHomDescent.compositionChoices_relative_extension hcof hfib P j f g c d e i q
example {L : SSet.{v}}
    (q : L ⟶ OrdinaryBarRelativeHomDescent.compositionChoices hcof hfib P j f g c d e) :
    T ◁ (SSet.stdSimplex.δ (1 : Fin 3) ▷ L) ≫
      OrdinaryBarRelativeHomDescent.compositionChoiceFamily hcof hfib P j f g c d e q =
    T ◁ fst (SSet.stdSimplex.obj (SimplexCategory.mk 1)) L ≫
      (OrdinaryBarRelativeHomDescent.nativeRestrictionComparison hcof hfib P j
        (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e).h :=
  OrdinaryBarRelativeHomDescent.compositionChoiceFamily_one hcof hfib P j f g c d e q

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ComparisonTriangleHorn,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ComparisonTriangleChoices,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarCompositionChoices]
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
  unless modules.size == expected.size do throwError "Missing triangle choice modules"
  logInfo m!"Triangle choice audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
