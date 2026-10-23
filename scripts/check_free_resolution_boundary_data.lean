import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegeneracyValues

universe v u vD uD
noncomputable section
open CategoryTheory
open SerrePositivity.HomotopyFunctionComplex

section Faces
open FreeGeneratorCategories FreeGeneratorFaces
variable (D : Type uD) [Category.{vD} D]
example (n : ℕ) (i : Fin (n + 1)) : faceHom D n i ≫ eqToHom (degree_power D n) =
    eqToHom (degree_power D (n + 1)) ≫
      ComonadResolutionOperators.face FreePathResolution.comonad
        (FreePathResolutionPresentation.base D) n i := face_comparison D n i
example (n : ℕ) (i : Fin (n + 1)) (X : D) : (fixedFace D n i).obj X = X := rfl
example (n : ℕ) (j k : Fin (n + 2)) (hjk : j < k) :
    fixedFace D (n + 1) j ⋙ fixedFace D n (k.pred (Fin.ne_zero_of_lt hjk)) =
      fixedFace D (n + 1) k ⋙ fixedFace D n (j.castPred (Fin.ne_last_of_lt hjk)) :=
  fixedFace_overlap D n j k hjk
end Faces

section Parameters
open OrdinaryBarFreeResolutionDegeneracyValues
example (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    sigma.{v} (n + 1) i.castSucc ≫ sigma n j = sigma (n + 1) j.succ ≫ sigma n i :=
  sigma_sigma n i j h
end Parameters

section ChoiceData
open CategoryTheory.MonoidalCategory FreeGeneratorCategories FreeGeneratorDegeneracies
open FreeGeneratorFaces OrdinaryBarChoiceBoundaryGluing OrdinaryBarFreeDiagramExtension
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (D : Type uD) [Category.{vD} D] (n : ℕ) (P : SSet.{max u v})
  (F : degree D (n + 2) ⥤ target (C := C) hcof hfib (parameters P (n + 1)))
  (G : degree D (n + 1) ⥤ target (C := C) hcof hfib (parameters P n))
  (faceLaw : ∀ i : Fin (n + 2), F ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ i) =
      fixedFace D (n + 1) i ⋙ G)
  (degeneracyLaw : ∀ i : Fin (n + 1), degeneracyFunctor D n i ⋙ F =
    G ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib
      (P ◁ OrdinaryBarFreeResolutionDegeneracyValues.sigma n i))

open OrdinaryBarFreeResolutionBoundary in
example (k : Fin (n + 3)) : boundary hcof hfib D n P F G faceLaw ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι k) =
      fixedFace D (n + 2) k ⋙ F := boundary_face hcof hfib D n P F G faceLaw k

open OrdinaryBarFreeResolutionDegeneracyValues in
example (X Y : D) : FreeGeneratorLatchingValues.Compatible n
    (fun i (p : hom (n + 1) X Y) => value hcof hfib D n P F i p) :=
  values_compatible hcof hfib D n P F G degeneracyLaw X Y

open OrdinaryBarFreeResolutionDegeneracyValues in
example (i : Fin (n + 2)) {X Y : D} (p : hom (n + 1) X Y)
    (he : FreeGeneratorLatchingValues.Fixed n (degeneracy (n + 1) i p)) :
    prescribedValue hcof hfib D n P F (degeneracy (n + 1) i p) he = value hcof hfib D n P F i p :=
  prescribedValue_degeneracy hcof hfib D n P F G degeneracyLaw i p he

open OrdinaryBarFreeResolutionDegeneracyValues in
example (i : Fin (n + 2)) :
    Paths.lift (V := degree D (n + 1)) (generators hcof hfib D n P F i) =
      F ⋙ OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ sigma (n + 1) i) :=
  diagram_from_generators hcof hfib D n P F i
end ChoiceData

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorFaces,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeResolutionBoundary,
    Name.str `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex
      "OrdinaryBarFreeResolutionDegeneracyValues"]
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
    throwError "Missing free resolution boundary data modules"
  logInfo m!"Free resolution boundary data audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
