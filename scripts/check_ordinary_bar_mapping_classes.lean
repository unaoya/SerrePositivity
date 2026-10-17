import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u vH uH
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

-- The source, localization and Hom universes are independent; no SSet model is assumed.
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]

example (b : Cᵒᵖ × C) : LocalizedHomDiagram.value Q b ≃
    (Q.obj b.1.unop ⟶ Q.obj b.2) := LocalizedHomDiagram.equiv Q b

example : OrdinaryResolutionPairs.raw (C := C) ⟶
    OrdinaryResolutionPairs.projection ⋙ LocalizedHomDiagram.spaces Q :=
  OrdinaryMappingClassLabel.comparison Q

example : OrdinaryResolutionBar.functor (C := C) ⟶
    LocalizedHomDiagram.spaces Q ⋙ SSet.uliftFunctor.{max u v, v} :=
  OrdinaryBarMappingClasses.augmentation Q

-- Recover the original fraction label as a full simplicial map, not only on vertices.
example (R : OrdinaryResolutionPairs.Index (C := C)) :
    OrdinaryBarMappingClasses.entry R ≫
      (OrdinaryBarMappingClasses.augmentation Q).app (OrdinaryResolutionPairs.projection.obj R) =
    SSet.uliftFunctor.{max u v, v}.map ((OrdinaryMappingClassLabel.comparison Q).app R) :=
  OrdinaryBarMappingClasses.entry_augmentation Q R

example {b c : Cᵒᵖ × C} (f : b ⟶ c)
    (z : SSet.π₀ (OrdinaryResolutionBar.functor.obj b)) :
    OrdinaryBarMappingClasses.piZeroLabel Q c
        (SSet.mapπ₀ (OrdinaryResolutionBar.functor.map f) z) =
      (LocalizedHomDiagram.types Q).map f (OrdinaryBarMappingClasses.piZeroLabel Q b z) :=
  OrdinaryBarMappingClasses.piZeroLabel_base Q f z

example (b : Cᵒᵖ × C) (n : SimplexCategoryᵒᵖ) :
    Small.{v} (Quotient ((OrdinaryBarMappingClasses.kernel Q).rel b n)) :=
  OrdinaryBarMappingClasses.kernel_small Q b n

-- This output is deliberately a coarse class quotient, with no boundary-lifting assertion.
example : Cᵒᵖ × C ⥤ SSet.{v} := OrdinaryBarMappingClasses.coarseQuotient Q

example (R : DiagramQuotient.Congruence (OrdinaryResolutionBar.functor (C := C)))
    (hR : ∀ b n {x y}, (R.rel b n).r x y →
      OrdinaryBarMappingClasses.label Q b n x = OrdinaryBarMappingClasses.label Q b n y) :
    DiagramQuotient.projection R ≫ OrdinaryBarMappingClasses.descend Q R hR =
      OrdinaryBarMappingClasses.augmentation Q :=
  OrdinaryBarMappingClasses.descend_factorization Q R hR

example (b : Cᵒᵖ × C) (n : SimplexCategoryᵒᵖ)
    (x y : (OrdinaryResolutionBar.functor.obj b).obj n) :
    Quotient.mk ((OrdinaryBarMappingClasses.kernel Q).rel b n) x =
        Quotient.mk ((OrdinaryBarMappingClasses.kernel Q).rel b n) y ↔
      OrdinaryBarMappingClasses.label Q b n x = OrdinaryBarMappingClasses.label Q b n y :=
  OrdinaryBarMappingClasses.quotient_eq_iff_label_eq Q b n x y

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.DiagramQuotient,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.LocalizedHomDiagram,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryMappingClassLabel,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarMappingClasses]
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
    throwError "Missing ordinary bar mapping class modules"
  logInfo m!"Ordinary bar mapping class audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
