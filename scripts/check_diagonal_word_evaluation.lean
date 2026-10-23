import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation

universe u v r
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.SimplicialModel
open OrdinaryBarFreeResolutionSeed FreeGeneratorCategories

section Source
variable (C : Type u) [Category.{v} C]
example : SimplicialObject Cat.{max u v, u} := OrdinaryBarFixedSource.literal C
example {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (X : D C) :
    ((OrdinaryBarFixedSource.literal C).map θ).toFunctor.obj X = X := rfl
example (n : SimplexCategoryᵒᵖ) (X : D C) :
    (OrdinaryBarFixedSource.projection C n).obj X = X := OrdinaryBarFixedSource.projection_obj C n X
example : OrdinaryBarFixedWordResolution.diagram C ≅ OrdinaryBarWordResolution.diagonal C :=
  OrdinaryBarFixedWordResolution.comparisonIso C
example (X Y : D C) : SSet.{max u v} := OrdinaryBarFixedWordResolution.hom C X Y
end Source

section Point
example {P : SSet.{r}} {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (x : P.obj n) :
    (OrdinaryBarDiagonalEvaluation.parameters P n).map θ (OrdinaryBarDiagonalEvaluation.point n x) =
      (P ◁ SSet.stdSimplex.map θ.unop).app m
        (OrdinaryBarDiagonalEvaluation.point m (P.map θ x)) :=
  OrdinaryBarDiagonalEvaluation.point_naturality θ x
end Point

section Actual
open OrdinaryBarDiagonalEvaluation
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})
example {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    OrdinaryBarFixedSource.literalMap C θ ⋙ OrdinaryBarFixedChoices.action hcof hfib P m =
      OrdinaryBarFixedChoices.action hcof hfib P n ⋙
        ParameterCategory.reindex (P ◁ SSet.stdSimplex.map θ.unop) :=
  OrdinaryBarFixedChoices.action_naturality hcof hfib P θ
example {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (k : SimplexCategoryᵒᵖ)
    (t : (OrdinaryBarFreeResolutionAction.parameters P m).obj k) :
    SerrePositivity.RetractWords.map (OrdinaryBarFixedSource.literalMap C θ)
        (MonoidWithZeroHom.id (WordSegment.degree.{max u v} k)) ⋙
      OrdinaryBarWordPresentation.largeEvaluation (C := C) hcof hfib P m.unop.len k t =
      OrdinaryBarWordPresentation.largeEvaluation (C := C) hcof hfib P n.unop.len k
        ((P ◁ SSet.stdSimplex.map θ.unop).app k t) :=
  OrdinaryBarFixedWordEvaluation.evaluation_map hcof hfib P θ k t
variable {T : SSet.{v}} (j : UniverseLift.obj.{max u v} T ⟶ P)
example {X Y : D C}
    (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y) :
    OrdinaryBarRetractSystem.small hcof hfib X ⊗ T ⟶ OrdinaryBarRetractSystem.small hcof hfib Y :=
  family hcof hfib P j f
example {X Y Z : D C}
    (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
    (g : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z) :
    ParameterComposition.comp (family hcof hfib P j f) (family hcof hfib P j g) =
      family hcof hfib P j (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) :=
  family_comp hcof hfib P j f g
example (X : D C) :
    family hcof hfib P j
      (SSet.stdSimplex.isTerminalObj₀.from _ ≫ OrdinaryBarFixedWordResolution.identity C X) =
      fst (OrdinaryBarRetractSystem.small hcof hfib X) T := family_identity hcof hfib P j X
example {U : SSet.{v}} (i : U ⟶ T) {X Y : D C}
    (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y) :
    family hcof hfib P (UniverseLift.map i ≫ j) (UniverseLift.map i ≫ f) =
      ParameterComposition.substitute i (family hcof hfib P j f) :=
  family_substitute hcof hfib P j i f
end Actual

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let modulePrefix := `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex
  let expected := #[Name.str modulePrefix "OrdinaryBarFixedSource",
    Name.str modulePrefix "OrdinaryBarFixedChoices",
    Name.str modulePrefix "OrdinaryBarFixedWordEvaluation",
    Name.str modulePrefix "OrdinaryBarFixedWordResolution",
    Name.str modulePrefix "OrdinaryBarDiagonalEvaluation"]
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
  unless modules.size == expected.size do throwError "Missing diagonal word evaluation modules"
  logInfo m!"Diagonal word evaluation audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
