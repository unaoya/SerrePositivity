import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u uI vI uB vB
noncomputable section
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.SimplicialModel

-- Reindexing is an actual natural bar map, without a model or a cofinality assumption.
example {E D : Type uI} [Category.{vI} E] [Category.{vI} D]
    {B : Type uB} [Category.{vB} B] (q : E ⥤ D) (p : D ⥤ B) (F : D ⥤ SSet.{v}) :
    BarConstruction.relative (q ⋙ p) (q ⋙ F) ⟶ BarConstruction.relative p F :=
  BarConstruction.reindex q p F

variable {C : Type u} [Category.{v} C] [ModelCategory C]

-- These are equalities of full strict functors, including every actual map.
example : OrdinaryResolutionPairs.forgetFrames (C := C) ⋙ OrdinaryResolutionPairs.raw =
    MixedBiresolutionComparison.functor := OrdinaryResolutionPairs.raw_eq
example : OrdinaryResolutionPairs.forgetFrames (C := C) ⋙ OrdinaryResolutionPairs.projection =
    RightResolutionMapping.projection := OrdinaryResolutionPairs.projection_eq

-- The complete row diagram now lives strictly inside the actual ordinary comma category.
example (R : RightResolutionMapping.Index C) :
    SimplexCategoryᵒᵖ ⥤ OrdinaryResolutionRows.Comma R := OrdinaryResolutionRows.commaRows R
example (R : RightResolutionMapping.Index C) :
    (Functor.const SimplexCategoryᵒᵖ).obj (OrdinaryResolutionRows.reference R) ⟶
      OrdinaryResolutionRows.commaRows R := OrdinaryResolutionRows.commaAugmentation R

example (R : RightResolutionMapping.Index C) :
    OrdinaryResolutionRows.rows R ⋙ OrdinaryResolutionPairs.raw =
      (ResolutionRowMixedMapping.rows (C := C)).flip.obj R := OrdinaryResolutionRows.raw_eq R

-- Every original Hom label is retained by the actual framed-to-ordinary bar map.
example (b : Cᵒᵖ × C) (n : SimplexCategoryᵒᵖ)
    (c : ((OrdinaryResolutionBar.framed (C := C)).obj b).obj n) (i : Fin (n.unop.len + 1)) :
    ((((OrdinaryResolutionBar.comparison (C := C)).app b).app n c).obj i).left.val =
      (c.obj i).left.val := OrdinaryResolutionBar.comparison_label b n c i

example {b c : Cᵒᵖ × C} (f : b ⟶ c) :
    (OrdinaryResolutionBar.framed (C := C)).map f ≫ OrdinaryResolutionBar.comparison.app c =
      OrdinaryResolutionBar.comparison.app b ≫ (OrdinaryResolutionBar.functor (C := C)).map f :=
  OrdinaryResolutionBar.comparison.naturality f

-- The retained left leg is the hom component of the actual localized natural isomorphism.
example (R : RightResolutionMapping.Index C) :
    (OrdinaryResolutionBar.leftAnodyneIso (C := C)).hom.app R =
      AnodyneHomotopy.anodyneQ.map ((OrdinaryResolutionBar.left (C := C)).app R) :=
  OrdinaryResolutionBar.leftAnodyneIso_hom R

example [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    (R : RightResolutionMapping.Index C) (n : SimplexCategoryᵒᵖ) :
    weakEquivalences SSet.{v} ((OrdinaryResolutionPairs.raw (C := C)).map
      ((OrdinaryResolutionRows.augmentation R).app n)) :=
  OrdinaryResolutionRows.raw_augmentation_weakEquivalence R hcof hfib n

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarReindex,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryResolutionPairs,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryResolutionRows,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryResolutionBar]
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
    throwError "Some ordinary resolution bar modules were not audited"
  logInfo m!"Ordinary resolution bar audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
