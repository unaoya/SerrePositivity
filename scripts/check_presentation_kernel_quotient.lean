import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.PresentationKernelQuotient

universe v w uB vB u uD vD
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex

section General
variable {B : Type uB} [Category.{vB} B] {F : B ⥤ SSet.{max w v}} {K : B ⥤ SSet.{v}}
  (a : F ⟶ K ⋙ SSet.uliftFunctor.{max w v, v})
  (hK : ∀ b, SSet.modelCategoryQuillen.J.rlp (terminal.from (K.obj b)))
  (ha : ∀ b, IsIso (AnodyneHomotopy.anodyneQ.map (a.app b)))

-- The relation is built from a functorial value-side factorization.
example : SmallTargetKernelQuotient.unit a ≫ SmallTargetKernelQuotient.projection a = a :=
  SmallTargetKernelQuotient.factorization a

example (b : B) (n : SimplexCategoryᵒᵖ) :
    Small.{v} (Quotient ((SmallTargetKernelQuotient.relation a).rel b n)) :=
  SmallTargetKernelQuotient.quotient_small a b n

example (b : B) : SSet.modelCategoryQuillen.I.rlp
    ((DiagramQuotient.projection (SmallTargetKernelQuotient.relation a)).app b) :=
  SmallTargetKernelQuotient.quotient_boundary_rlp a hK ha b
end General

section Actual
variable {C : Type u} [Category.{v} C] [ModelCategory C]

-- No relation or lifting certificate is an input, nor any simplicial model structure.
example : DiagramQuotient.Congruence (PresentationKernelQuotient.enlarged (C := C)) :=
  PresentationKernelQuotient.relation

example (R : RightResolutionMapping.Index C) (n : SimplexCategoryᵒᵖ) :
    Small.{v} (Quotient ((PresentationKernelQuotient.relation (C := C)).rel R n)) :=
  PresentationKernelQuotient.quotient_small R n

example (R : RightResolutionMapping.Index C) : SSet.modelCategoryQuillen.I.rlp
    ((DiagramQuotient.projection (PresentationKernelQuotient.relation (C := C))).app R) :=
  PresentationKernelQuotient.quotient_boundary_rlp R

-- The base remains the entire presentation category; no descent section is asserted.
example : RightResolutionMapping.Index C ⥤ SSet.{v} :=
  PresentationKernelQuotient.functor

example (R : RightResolutionMapping.Index C) : SSet.modelCategoryQuillen.J.rlp
    (terminal.from ((PresentationKernelQuotient.functor (C := C)).obj R)) :=
  PresentationKernelQuotient.terminal_rlp R

example (R : RightResolutionMapping.Index C) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((PresentationKernelQuotient.left (C := C)).app R)) :=
  PresentationKernelQuotient.left_localized_isIso R

example {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    OrdinaryResolutionBar.middle (C := C) ⋙ L ≅
      (PresentationKernelQuotient.functor ⋙ SSet.uliftFunctor.{max u v, v}) ⋙ L :=
  PresentationKernelQuotient.leftImageIso L hL

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

example {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    (PresentationKernelQuotient.functor (C := C) ⋙ SSet.uliftFunctor.{max u v, v}) ⋙ L ≅
      (RightResolutionMapping.projection ⋙ OrdinaryResolutionBar.functor) ⋙ L :=
  PresentationKernelQuotient.baseComparisonIso hcof hfib L hL

example {R S : RightResolutionMapping.Index C} (f : R ⟶ S)
    (hs : weakEquivalences C ((RightResolutionMapping.projection.map f).1.unop))
    (ht : weakEquivalences C ((RightResolutionMapping.projection.map f).2)) :
    weakEquivalences SSet.{v} ((PresentationKernelQuotient.functor (C := C)).map f) :=
  PresentationKernelQuotient.map_weakEquivalence hcof hfib f hs ht
end Actual

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SmallTargetKernelQuotient,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.PresentationKernelQuotient]
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
    throwError "Missing presentation kernel quotient modules"
  logInfo m!"Presentation kernel quotient audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
