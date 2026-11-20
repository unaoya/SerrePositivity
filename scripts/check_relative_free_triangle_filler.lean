import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeTriangleFiller

universe v u w
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.HomotopyFunctionComplex

-- Independent object and Hom universes; no model structure in the image intersection theorem.
section Paths
variable {D : Type u} [Category.{v} D] {X Y : D} (p q : Quiver.Path X Y)
example : Quiver.Hom.toPath (V := Paths D) q = (FreePathResolution.duplicate D).map p ↔
    ∃ f : X ⟶ Y, p = f.toPath ∧ q = f.toPath :=
  FreePathDegeneracyImage.generator_image_intersection p q
example : Function.Injective (fun r : Quiver.Path X Y => (FreePathResolution.duplicate D).map r) :=
  FreePathDegeneracyImage.duplicate_map_injective
end Paths

-- Parameter identities also require no model structure.
section Parameters
open SerrePositivity.SimplicialModel.TriangleDegeneracyParameters
example : SSet.stdSimplex.δ (0 : Fin 3) ≫ sigma.{w} 0 = 𝟙 _ := face0_sigma0
example : SSet.stdSimplex.δ (1 : Fin 3) ≫ sigma.{w} 0 = 𝟙 _ := face1_sigma0
example : SSet.stdSimplex.δ (1 : Fin 3) ≫ sigma.{w} 1 = 𝟙 _ := face1_sigma1
example : SSet.stdSimplex.δ (2 : Fin 3) ≫ sigma.{w} 1 = 𝟙 _ := face2_sigma1
example : SSet.stdSimplex.δ (0 : Fin 3) ≫ sigma.{w} 1 =
    SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1) := face0_sigma1
example : SSet.stdSimplex.δ (2 : Fin 3) ≫ sigma.{w} 0 =
    SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0) := face2_sigma0
end Parameters

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

section BoundaryExt
variable {P : SSet.{max u v}} {n : ℕ}
  {X Y : OrdinaryBarChoiceCategory.Object (C := C) hcof hfib
    (P ⊗ (SSet.boundary (n + 1)).toSSet)} (a b : X ⟶ Y)
example (h : ∀ k : Fin (n + 2),
    (OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι k)).map a =
      (OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι k)).map b) : a = b :=
  OrdinaryBarChoiceBoundaryExt.hom_ext hcof hfib a b h
end BoundaryExt

section Actual
variable (P : SSet.{max u v})
open OrdinaryBarFreeTriangleFiller

-- The whole pre-existing boundary is retained, not merely its vertices or edges separately.
example : filler (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (OrdinaryBarFreeTriangleDegeneracy.inclusion P) =
      OrdinaryBarFreeTriangleGluing.boundary hcof hfib P := filler_boundary hcof hfib P

example : filler (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ (0 : Fin 3)) =
      OrdinaryBarFreeTriangleBoundary.edge12 hcof hfib P := filler_face0 hcof hfib P

example : filler (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ (1 : Fin 3)) =
      OrdinaryBarFreeTriangleBoundary.edge02 hcof hfib P := filler_face1 hcof hfib P

example : filler (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.stdSimplex.δ (2 : Fin 3)) =
      OrdinaryBarFreeTriangleBoundary.edge01 hcof hfib P := filler_face2 hcof hfib P

example : FreePathResolutionDegreeTwo.degeneracyZero (Cᵒᵖ × C) ⋙ filler hcof hfib P =
    OrdinaryBarFreeTriangleDegeneracy.triangle hcof hfib P 1 :=
  filler_degeneracyZero hcof hfib P

example : FreePathResolutionDegreeTwo.degeneracyOne (Cᵒᵖ × C) ⋙ filler hcof hfib P =
    OrdinaryBarFreeTriangleDegeneracy.triangle hcof hfib P 0 :=
  filler_degeneracyOne hcof hfib P

example {X Y : Cᵒᵖ × C} (e : Quiver.Path (V := Paths (Cᵒᵖ × C)) X Y)
    (hl : Left e) (hr : Right e) : valueLeft hcof hfib P e = valueRight hcof hfib P e :=
  values_agree hcof hfib P e hl hr
end Actual

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryExt,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreePathDegeneracyImage,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.TriangleDegeneracyParameters,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeTriangleFiller]
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
    throwError "Missing relative free triangle filler modules"
  logInfo m!"Relative free triangle filler audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
