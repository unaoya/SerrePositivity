import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses

universe w uD vD v u vH uH
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex

-- The base size and its Hom size are independent of the value universe.
example {D : Type uD} [Category.{vD} D] {F : D ⥤ SSet.{w}} {T : D ⥤ Type w}
    (a : F ⟶ T ⋙ Functor.const SimplexCategoryᵒᵖ) :
    Functor.whiskerLeft F AnodyneKanReplacement.unit ≫
      DiscreteKanExtension.naturalExtension a = a :=
  DiscreteKanExtension.naturalExtension_fac a

example {D : Type uD} [Category.{vD} D] {F : D ⥤ SSet.{w}} {T : D ⥤ Type w}
    (a : F ⟶ T ⋙ Functor.const SimplexCategoryᵒᵖ)
    (b : F ⋙ AnodyneKanReplacement.functor ⟶ T ⋙ Functor.const SimplexCategoryᵒᵖ)
    (hb : Functor.whiskerLeft F AnodyneKanReplacement.unit ≫ b = a) :
    b = DiscreteKanExtension.naturalExtension a :=
  DiscreteKanExtension.naturalExtension_unique a b hb

section Bar
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]

-- No simplicial model structure is used for the actual Kan replacement or its label.
example (b : Cᵒᵖ × C) : SSet.modelCategoryQuillen.J.rlp
    (terminal.from ((OrdinaryKanBarMappingClasses.functor (C := C)).obj b)) :=
  OrdinaryKanBarMappingClasses.terminal_rlp b

example : OrdinaryKanBarMappingClasses.unit ≫ OrdinaryKanBarMappingClasses.augmentation Q =
    OrdinaryBarMappingClasses.augmentation Q :=
  OrdinaryKanBarMappingClasses.unit_augmentation Q

example (a : OrdinaryKanBarMappingClasses.functor (C := C) ⟶
    LocalizedHomDiagram.spaces Q ⋙ SSet.uliftFunctor.{max u v, v})
    (ha : OrdinaryKanBarMappingClasses.unit ≫ a = OrdinaryBarMappingClasses.augmentation Q) :
    a = OrdinaryKanBarMappingClasses.augmentation Q :=
  OrdinaryKanBarMappingClasses.augmentation_unique Q a ha

example (b : Cᵒᵖ × C) :
    Function.Bijective (SSet.mapπ₀ ((OrdinaryKanBarMappingClasses.unit (C := C)).app b)) :=
  OrdinaryKanBarMappingClasses.unit_piZero_bijective b

example (b : Cᵒᵖ × C) (n : SimplexCategoryᵒᵖ) :
    Small.{v} (Quotient ((OrdinaryKanBarMappingClasses.kernel Q).rel b n)) :=
  OrdinaryKanBarMappingClasses.kernel_small Q b n

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

example (b : Cᵒᵖ × C) : Function.Bijective
    (OrdinaryKanBarMappingClasses.piZeroLabel Q b) :=
  OrdinaryKanBarMappingClasses.piZeroLabel_bijective Q hcof hfib b

example (b : Cᵒᵖ × C) :
    SSet.π₀ (OrdinaryKanBarMappingClasses.functor.obj b) ≃
      (Q.obj b.1.unop ⟶ Q.obj b.2) :=
  OrdinaryKanBarMappingClasses.piZeroEquiv Q hcof hfib b

example (b : Cᵒᵖ × C) (z : SSet.π₀ (OrdinaryResolutionBar.functor.obj b)) :
    OrdinaryKanBarMappingClasses.piZeroEquiv Q hcof hfib b
        (SSet.mapπ₀ (OrdinaryKanBarMappingClasses.unit.app b) z) =
      OrdinaryBarPiZero.piZeroEquiv hcof hfib Q b z :=
  OrdinaryKanBarMappingClasses.piZeroEquiv_unit Q hcof hfib b z

example {b c : Cᵒᵖ × C} (f : b ⟶ c)
    (z : SSet.π₀ (OrdinaryKanBarMappingClasses.functor.obj b)) :
    OrdinaryKanBarMappingClasses.piZeroEquiv Q hcof hfib c
        (SSet.mapπ₀ (OrdinaryKanBarMappingClasses.functor.map f) z) =
      Q.map f.1.unop ≫ OrdinaryKanBarMappingClasses.piZeroEquiv Q hcof hfib b z ≫ Q.map f.2 :=
  OrdinaryKanBarMappingClasses.piZeroEquiv_naturality Q hcof hfib f z

example {b c : Cᵒᵖ × C} (f : b ⟶ c)
    (hs : weakEquivalences C f.1.unop) (ht : weakEquivalences C f.2) :
    IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryKanBarMappingClasses.functor.map f)) :=
  OrdinaryKanBarMappingClasses.map_localized_isIso hcof hfib f hs ht
end Bar

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.DiscreteKanExtension,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses]
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
    throwError "Missing ordinary Kan bar mapping-class modules"
  logInfo m!"Ordinary Kan bar mapping-class audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
