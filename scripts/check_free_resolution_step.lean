import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionTower

universe v u vD uD
noncomputable section
open CategoryTheory
open SerrePositivity.HomotopyFunctionComplex

section Source
open FreeGeneratorCategories FreeGeneratorMixedOperators
variable (D : Type uD) [Category.{vD} D]
example (n : ℕ) (i : Fin (n + 1)) :
    degeneracyFunctor D n i ⋙ rawFace D (n + 1) i.castSucc = 𝟭 _ :=
  degeneracy_face_self D n i
example (n : ℕ) (i : Fin (n + 1)) :
    degeneracyFunctor D n i ⋙ rawFace D (n + 1) i.succ = 𝟭 _ :=
  degeneracy_face_succ D n i
example (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i ≤ j.castSucc) :
    degeneracyFunctor D (n + 1) j.succ ⋙ rawFace D (n + 2) i.castSucc =
      rawFace D (n + 1) i ⋙ degeneracyFunctor D n j := degeneracy_face_le D n i j h
example (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i) :
    degeneracyFunctor D (n + 1) j.castSucc ⋙ rawFace D (n + 2) i.succ =
      rawFace D (n + 1) i ⋙ degeneracyFunctor D n j := degeneracy_face_gt D n i j h
end Source

section Step
open CategoryTheory.MonoidalCategory FreeGeneratorCategories FreeGeneratorMixedOperators
open OrdinaryBarChoiceBoundaryGluing OrdinaryBarFreeDiagramExtension
open OrdinaryBarFreeResolutionDegeneracyValues
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (D : Type uD) [Category.{vD} D] (n : ℕ) (P : SSet.{max u v})
  (F : degree D (n + 2) ⥤ target (C := C) hcof hfib (parameters P (n + 1)))
  (G : degree D (n + 1) ⥤ target (C := C) hcof hfib (parameters P n))
  (faceLaw : ∀ i : Fin (n + 2), F ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ i) =
      FreeGeneratorFaces.fixedFace D (n + 1) i ⋙ G)
  (degeneracyLaw : ∀ i : Fin (n + 1), degeneracyFunctor D n i ⋙ F =
    G ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ sigma n i))

open SerrePositivity.SimplicialModel.ReversedSimplexParameters in
example (j : Fin (n + 2)) (i : Fin (n + 3)) :
    degeneracyFunctor D (n + 1) j ⋙ (rawFace D (n + 2) i ⋙ F) =
      diagram hcof hfib D n P F j ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ delta (n + 1) i) :=
  OrdinaryBarFreeResolutionMixedFaces.facet_equation hcof hfib D n P F G faceLaw degeneracyLaw j i

example (j : Fin (n + 2)) : degeneracyFunctor D (n + 1) j ⋙
    OrdinaryBarFreeResolutionBoundary.boundary hcof hfib D n P F G faceLaw =
      diagram hcof hfib D n P F j ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ (SSet.boundary (n + 2)).ι) :=
  OrdinaryBarFreeResolutionDegenerateBoundary.boundary_degeneracy
    hcof hfib D n P F G faceLaw degeneracyLaw j

open OrdinaryBarFreeResolutionStep in
example (k : Fin (n + 3)) : filler hcof hfib D n P F G faceLaw degeneracyLaw ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ k) =
      FreeGeneratorFaces.fixedFace D (n + 2) k ⋙ F :=
  filler_face hcof hfib D n P F G faceLaw degeneracyLaw k

open OrdinaryBarFreeResolutionStep in
example (i : Fin (n + 2)) : degeneracyFunctor D (n + 1) i ⋙
    filler hcof hfib D n P F G faceLaw degeneracyLaw =
      F ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ sigma (n + 1) i) :=
  filler_degeneracy hcof hfib D n P F G faceLaw degeneracyLaw i
end Step

section Tower
open CategoryTheory.MonoidalCategory FreeGeneratorCategories OrdinaryBarFreeResolutionTower
open OrdinaryBarFreeResolutionDegeneracyValues
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (D : Type uD) [Category.{vD} D] (P : SSet.{max u v})
  (A : Seed (C := C) hcof hfib D P)
example : OrdinaryBarFreeResolutionTower.diagram hcof hfib D P A 0 = A.previous := rfl
example : OrdinaryBarFreeResolutionTower.diagram hcof hfib D P A 1 = A.current := rfl
example (m : ℕ) (i : Fin (m + 2)) :
    OrdinaryBarFreeResolutionTower.diagram hcof hfib D P A (m + 1) ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ i) =
    FreeGeneratorFaces.fixedFace D (m + 1) i ⋙
      OrdinaryBarFreeResolutionTower.diagram hcof hfib D P A m :=
  diagram_face hcof hfib D P A m i
example (m : ℕ) (i : Fin (m + 1)) : degeneracyFunctor D m i ⋙
    OrdinaryBarFreeResolutionTower.diagram hcof hfib D P A (m + 1) =
      OrdinaryBarFreeResolutionTower.diagram hcof hfib D P A m ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ sigma m i) :=
  diagram_degeneracy hcof hfib D P A m i
end Tower

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let modulePrefix := `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex
  let expected := #[
    Name.str modulePrefix "FreeGeneratorMixedOperators",
    `SerrePositivity.HomotopicalAlgebra.Simplicial.ReversedSimplexParameters,
    Name.str modulePrefix "OrdinaryBarFreeResolutionMixedFaces",
    Name.str modulePrefix "OrdinaryBarFreeResolutionDegenerateBoundary",
    Name.str modulePrefix "OrdinaryBarFreeResolutionStep",
    Name.str modulePrefix "OrdinaryBarFreeResolutionTower"]
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
    throwError "Missing free resolution step modules"
  logInfo m!"Free resolution step audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
