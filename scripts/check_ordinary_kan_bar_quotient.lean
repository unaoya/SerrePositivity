import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarQuotient

universe w uB vB v u uD vD vH uH
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex

-- Every pointwise localized equivalence supports unique strict discrete-valued descent.
example {B : Type uB} [Category.{vB} B] {F G : B ⥤ SSet.{w}} {T : B ⥤ Type w}
    (p : F ⟶ G) (hp : ∀ b, IsIso (AnodyneHomotopy.anodyneQ.map (p.app b)))
    (a : F ⟶ T ⋙ Functor.const SimplexCategoryᵒᵖ) :
    p ≫ DiscreteLocalizedExtension.descend p hp a = a :=
  DiscreteLocalizedExtension.descend_fac p hp a

example {B : Type uB} [Category.{vB} B] {F G : B ⥤ SSet.{w}} {T : B ⥤ Type w}
    (p : F ⟶ G) (hp : ∀ b, IsIso (AnodyneHomotopy.anodyneQ.map (p.app b)))
    (a : F ⟶ T ⋙ Functor.const SimplexCategoryᵒᵖ)
    (b : G ⟶ T ⋙ Functor.const SimplexCategoryᵒᵖ) (hb : p ≫ b = a) :
    b = DiscreteLocalizedExtension.descend p hp a :=
  DiscreteLocalizedExtension.descend_unique p hp a b hb

section Certificate
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (d : OrdinaryKanBarQuotient.QuotientData (C := C))

-- The certificate is an explicit unfulfilled input, not inferred from ModelCategory C.
example : Cᵒᵖ ⥤ C ⥤ SSet.{v} := OrdinaryKanBarQuotient.curried d

-- These outputs do not require either value universe to have a model structure.
example (b : Cᵒᵖ × C) : SSet.modelCategoryQuillen.J.rlp
    (terminal.from ((OrdinaryKanBarQuotient.functor d).obj b)) :=
  OrdinaryKanBarQuotient.terminal_rlp d b

example {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    OrdinaryResolutionBar.functor (C := C) ⋙ L ≅
      (OrdinaryKanBarQuotient.functor d ⋙ SSet.uliftFunctor.{max u v, v}) ⋙ L :=
  OrdinaryKanBarQuotient.imageIso d L hL

example (e : OrdinaryKanBarQuotient.QuotientData (C := C))
    {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    (OrdinaryKanBarQuotient.functor d ⋙ SSet.uliftFunctor.{max u v, v}) ⋙ L ≅
      (OrdinaryKanBarQuotient.functor e ⋙ SSet.uliftFunctor.{max u v, v}) ⋙ L :=
  OrdinaryKanBarQuotient.changeQuotientIso d e L hL

variable {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]

-- Label preservation is a theorem from the certificate, not a fourth field.
example (b : Cᵒᵖ × C) (n : SimplexCategoryᵒᵖ)
    {x y : (OrdinaryKanBarMappingClasses.functor.obj b).obj n}
    (h : (d.relation.rel b n).r x y) :
    ((OrdinaryKanBarMappingClasses.augmentation Q).app b).app n x =
      ((OrdinaryKanBarMappingClasses.augmentation Q).app b).app n y :=
  OrdinaryKanBarQuotient.relation_preserves_labels d Q b n h

example : OrdinaryKanBarQuotient.comparison d ≫ OrdinaryKanBarQuotient.augmentation d Q =
    OrdinaryBarMappingClasses.augmentation Q :=
  OrdinaryKanBarQuotient.comparison_augmentation d Q

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

example {b c : Cᵒᵖ × C} (f : b ⟶ c)
    (hs : weakEquivalences C f.1.unop) (ht : weakEquivalences C f.2) :
    weakEquivalences SSet.{v} ((OrdinaryKanBarQuotient.functor d).map f) :=
  OrdinaryKanBarQuotient.map_weakEquivalence d hcof hfib f hs ht

example (b : Cᵒᵖ × C) : SSet.π₀ ((OrdinaryKanBarQuotient.functor d).obj b) ≃
    (Q.obj b.1.unop ⟶ Q.obj b.2) :=
  OrdinaryKanBarQuotient.piZeroEquiv d Q hcof hfib b

example {b c : Cᵒᵖ × C} (f : b ⟶ c)
    (z : SSet.π₀ ((OrdinaryKanBarQuotient.functor d).obj b)) :
    OrdinaryKanBarQuotient.piZeroEquiv d Q hcof hfib c
        (SSet.mapπ₀ ((OrdinaryKanBarQuotient.functor d).map f) z) =
      Q.map f.1.unop ≫ OrdinaryKanBarQuotient.piZeroEquiv d Q hcof hfib b z ≫ Q.map f.2 :=
  OrdinaryKanBarQuotient.piZeroEquiv_naturality d Q hcof hfib f z

example (b : Cᵒᵖ × C) (z : SSet.π₀ (OrdinaryResolutionBar.functor.obj b)) :
    OrdinaryKanBarQuotient.piZeroEquiv d Q hcof hfib b
        (UniverseLiftPiZero.down _
          (SSet.mapπ₀ ((OrdinaryKanBarQuotient.comparison d).app b) z)) =
      OrdinaryBarPiZero.piZeroEquiv hcof hfib Q b z :=
  OrdinaryKanBarQuotient.piZeroEquiv_comparison d Q hcof hfib b z
end Certificate

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.DiscreteLocalizedExtension,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarQuotient]
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
    throwError "Missing ordinary Kan bar quotient modules"
  logInfo m!"Ordinary Kan bar quotient audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
