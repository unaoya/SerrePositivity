import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice

universe v u vD uD
noncomputable section
open CategoryTheory
open SerrePositivity SerrePositivity.HomotopyFunctionComplex

section GeneralNaturality
variable {D : Type uD} [Category.{vD} D] (F G : SimplicialObject D)
  (a : ∀ n : SimplexCategoryᵒᵖ, F.obj n ⟶ G.obj n)
  (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), F.δ i ≫ a (Opposite.op (SimplexCategory.mk n)) =
    a (Opposite.op (SimplexCategory.mk (n + 1))) ≫ G.δ i)
  (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), F.σ i ≫
    a (Opposite.op (SimplexCategory.mk (n + 1))) =
      a (Opposite.op (SimplexCategory.mk n)) ≫ G.σ i)
example {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) : F.map θ ≫ a m = a n ≫ G.map θ :=
  SimplexNaturality.naturality F G a hδ hσ θ
example (n : SimplexCategoryᵒᵖ) :
    (SimplexNaturality.ofFacesDegeneracies F G a hδ hσ).app n = a n := rfl
end GeneralNaturality

section ActualChoices
open OrdinaryBarFreeResolutionNaturalChoice FreeGeneratorCategories OrdinaryBarFreeResolutionSeed
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

example : source (C := C) ⟶ target (C := C) hcof hfib P := choices hcof hfib P
example {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    (source (C := C)).map θ ≫ (choices hcof hfib P).app m =
      (choices hcof hfib P).app n ≫ (target hcof hfib P).map θ :=
  (choices hcof hfib P).naturality θ

example (n : SimplexCategoryᵒᵖ) : (choices (C := C) hcof hfib P).app n =
    eqToHom (degree_power (D C) (n.unop.len + 1)).symm ≫
      (OrdinaryBarFreeResolutionChoices.diagram hcof hfib P n.unop.len).toCatHom := rfl

example {n : ℕ} (i : Fin (n + 2)) : (source (C := C)).δ i ≫
    component hcof hfib P (Opposite.op (SimplexCategory.mk n)) =
      component hcof hfib P (Opposite.op (SimplexCategory.mk (n + 1))) ≫
        (target hcof hfib P).δ i := component_face hcof hfib P i
example {n : ℕ} (i : Fin (n + 1)) : (source (C := C)).σ i ≫
    component hcof hfib P (Opposite.op (SimplexCategory.mk (n + 1))) =
      component hcof hfib P (Opposite.op (SimplexCategory.mk n)) ≫
        (target hcof hfib P).σ i := component_degeneracy hcof hfib P i

example : choices (C := C) hcof hfib P ≫
    OrdinaryBarParameterChoiceCategory.projection hcof hfib P =
      Functor.whiskerLeft SimplexCategory.rev.op
        (FreePathSimplicialResolution.augmentation (Cᵒᵖ × C)) :=
  augmentation_eq_standard hcof hfib P
example (n : SimplexCategoryᵒᵖ) :
    (augmentation (C := C) hcof hfib P).app n =
      eqToHom (degree_power (D C) (n.unop.len + 1)).symm ≫
        (OrdinaryBarFreeResolutionChoices.augmentation (C := C) n.unop.len ⋙
          ULiftHom.up.{v, u, u}).toCatHom := augmentation_app hcof hfib P n
end ActualChoices

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.CategoryTheory.Simplex.Naturality,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarParameterChoiceCategory,
    Name.str `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex
      "OrdinaryBarFreeResolutionNaturalChoice"]
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
    throwError "Missing free resolution natural choice modules"
  logInfo m!"Free resolution natural choices audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
