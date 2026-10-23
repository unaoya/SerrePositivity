import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies

universe v u
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open FreeGeneratorCategories FreeGeneratorFaces OrdinaryBarFreeResolutionSeed
open OrdinaryBarChoiceBoundaryGluing OrdinaryBarFreeResolutionDegeneracyValues

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

open OrdinaryBarFreeResolutionAction in
example {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    ((source (C := C)).map θ).toFunctor ⋙ action hcof hfib P m =
      action hcof hfib P n ⋙ ParameterCategory.reindex (P ◁ SSet.stdSimplex.map θ.unop) :=
  action_naturality hcof hfib P θ

open OrdinaryBarFreeResolutionAction in
example (n : SimplexCategoryᵒᵖ) : choicesAt hcof hfib P n ⋙
    OrdinaryBarChoiceCategory.projection hcof hfib (parameters P n) =
      baseProjection (C := C) n := choicesAt_projection hcof hfib P n

-- The endpoints below are the literal original labels, with independent u and v.
open OrdinaryBarFreeAmbientFamilies in
example (n : ℕ) {X Y : D C} (f : FreeGeneratorDegeneracies.hom (n + 1) X Y) :
    OrdinaryBarRetractSystem.ambient hcof hfib X ⊗ parameters P n ⟶
      OrdinaryBarRetractSystem.ambient hcof hfib Y := family hcof hfib P n f

open OrdinaryBarFreeAmbientFamilies in
example (n : ℕ) {X Y Z : degree (D C) (n + 1)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    family hcof hfib P n (f ≫ g) =
      ParameterComposition.comp (family hcof hfib P n f) (family hcof hfib P n g) :=
  family_comp hcof hfib P n f g

open OrdinaryBarFreeAmbientFamilies in
example (n : ℕ) (X : D C) :
    family hcof hfib P n (FreeGeneratorCategories.identity (D C) (n + 1) X) =
      ParameterComposition.const (parameters P n)
        (𝟙 (OrdinaryBarRetractSystem.ambient hcof hfib X)) := family_id hcof hfib P n X

open OrdinaryBarFreeAmbientFamilies in
example (n : ℕ) (i : Fin (n + 2)) {X Y : degree (D C) (n + 2)} (f : X ⟶ Y) :
    ParameterComposition.substitute (P ◁ SSet.stdSimplex.δ i) (family hcof hfib P (n + 1) f) =
      family hcof hfib P n ((fixedFace (D C) (n + 1) i).map f) := family_face hcof hfib P n i f

open OrdinaryBarFreeAmbientFamilies in
example (n : ℕ) (i : Fin (n + 1)) {X Y : degree (D C) (n + 1)} (f : X ⟶ Y) :
    family hcof hfib P (n + 1) ((degeneracyFunctor (D C) n i).map f) =
      ParameterComposition.substitute (P ◁ sigma n i) (family hcof hfib P n f) :=
  family_degeneracy hcof hfib P n i f

open OrdinaryBarFreeTransferredFamilies OrdinaryBarRetractSystem in
example (n : ℕ) {X Y : D C} (f : FreeGeneratorDegeneracies.hom (n + 1) X Y) :
    parameters P n ⟶ UniverseLift.obj.{max u v}
      ((ihom (small hcof hfib X)).obj (small hcof hfib Y)) := transferred hcof hfib P n f

open OrdinaryBarFreeTransferredFamilies OrdinaryBarRetractSystem in
example (n : ℕ) (X : D C) :
    family hcof hfib P n (FreeGeneratorCategories.identity (D C) (n + 1) X) =
      fst (lifted hcof hfib X) (parameters P n) := family_id hcof hfib P n X

open OrdinaryBarFreeTransferredFamilies in
example (n : ℕ) (i : Fin (n + 2)) {X Y : degree (D C) (n + 2)} (f : X ⟶ Y) :
    transferred hcof hfib P n ((fixedFace (D C) (n + 1) i).map f) =
      P ◁ SSet.stdSimplex.δ i ≫ transferred hcof hfib P (n + 1) f :=
  transferred_face hcof hfib P n i f

open OrdinaryBarFreeTransferredFamilies in
example (n : ℕ) (i : Fin (n + 1)) {X Y : degree (D C) (n + 1)} (f : X ⟶ Y) :
    transferred hcof hfib P (n + 1) ((degeneracyFunctor (D C) n i).map f) =
      P ◁ sigma n i ≫ transferred hcof hfib P n f := transferred_degeneracy hcof hfib P n i f

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let modulePrefix := `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex
  let expected := #[Name.str modulePrefix "OrdinaryBarFreeResolutionAction",
    Name.str modulePrefix "OrdinaryBarFreeAmbientFamilies",
    Name.str modulePrefix "OrdinaryBarFreeTransferredFamilies"]
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
    throwError "Missing free resolution action modules"
  logInfo m!"Free resolution action audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
