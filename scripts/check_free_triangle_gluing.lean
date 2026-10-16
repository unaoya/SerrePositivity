import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleGluing

universe v u w
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

-- Any dimension and parameter space, with no model structure at all.
section Tensor
variable {T Q : SSet.{w}} {n : ℕ}
  (faces : Fin (n + 3) → (T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ Q))
  (hf : BoundaryTensorGluing.Compatible faces)
example (k : Fin (n + 3)) : T ◁ SSet.boundary.ι k ≫ BoundaryTensorGluing.desc faces hf =
    faces k := BoundaryTensorGluing.desc_fac faces hf k
example {f g : T ⊗ (SSet.boundary (n + 1)).toSSet ⟶ Q}
    (h : ∀ k : Fin (n + 2), T ◁ SSet.boundary.ι k ≫ f = T ◁ SSet.boundary.ι k ≫ g) :
    f = g := BoundaryTensorGluing.hom_ext h
end Tensor

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- Endpoint equalities supply base relabeling; no equality of the base arrows is assumed.
section Choices
variable {P : SSet.{max u v}}
  {X Y : OrdinaryBarChoiceCategory.Object (C := C) hcof hfib
    (P ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 1))} (a b c : X ⟶ Y)
  (h0 : (OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀).map a =
    (OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀).map b)
  (h1 : (OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁).map a =
    (OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀).map c)
  (h2 : (OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁).map b =
    (OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁).map c)
open OrdinaryBarChoiceTriangleGluing

example : (OrdinaryBarChoiceCategory.reindex hcof hfib
    (P ◁ SSet.boundary.ι (0 : Fin 3))).map (boundaryHom hcof hfib a b c h0 h1 h2) = c :=
  boundaryHom_face0 hcof hfib a b c h0 h1 h2

example : (OrdinaryBarChoiceCategory.reindex hcof hfib
    (P ◁ SSet.boundary.ι (1 : Fin 3))).map (boundaryHom hcof hfib a b c h0 h1 h2) = b :=
  boundaryHom_face1 hcof hfib a b c h0 h1 h2

example : (OrdinaryBarChoiceCategory.reindex hcof hfib
    (P ◁ SSet.boundary.ι (2 : Fin 3))).map (boundaryHom hcof hfib a b c h0 h1 h2) = a :=
  boundaryHom_face2 hcof hfib a b c h0 h1 h2
end Choices

-- The actual boundary on the original triple free category retains arbitrary existing P.
section Actual
variable (P : SSet.{max u v})

example : OrdinaryBarFreeTriangleGluing.boundary (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι (0 : Fin 3)) =
      OrdinaryBarFreeTriangleBoundary.edge12 hcof hfib P :=
  OrdinaryBarFreeTriangleGluing.boundary_face0 hcof hfib P

example : OrdinaryBarFreeTriangleGluing.boundary (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι (1 : Fin 3)) =
      OrdinaryBarFreeTriangleBoundary.edge02 hcof hfib P :=
  OrdinaryBarFreeTriangleGluing.boundary_face1 hcof hfib P

example : OrdinaryBarFreeTriangleGluing.boundary (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib (P ◁ SSet.boundary.ι (2 : Fin 3)) =
      OrdinaryBarFreeTriangleBoundary.edge01 hcof hfib P :=
  OrdinaryBarFreeTriangleGluing.boundary_face2 hcof hfib P

example : OrdinaryBarFreeTriangleGluing.boundary (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.projection hcof hfib _ =
      OrdinaryBarFreeTriangleBoundary.edge01 hcof hfib P ⋙
        OrdinaryBarChoiceCategory.projection hcof hfib _ :=
  OrdinaryBarFreeTriangleGluing.boundary_projection hcof hfib P
end Actual

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryTensorGluing,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceTriangleGluing,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleGluing]
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
    throwError "Missing free triangle gluing modules"
  logInfo m!"Free triangle gluing audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
