import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryQuotientPiZero

universe v w u vH uH
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.SimplicialModel

example (X : SSet.{v}) : SSet.π₀ (SSet.uliftFunctor.{w, v}.obj X) ≃ SSet.π₀ X :=
  UniverseLiftPiZero.equiv X

section Quotient
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]
  (R : DiagramQuotient.Congruence (OrdinaryResolutionBar.functor (C := C)))
  (hR : ∀ b n {x y}, (R.rel b n).r x y →
    OrdinaryBarMappingClasses.label Q b n x = OrdinaryBarMappingClasses.label Q b n y)

-- This surjectivity does not need a value model or finite-boundary lifting.
example (b : Cᵒᵖ × C) :
    Function.Surjective (SSet.mapπ₀ ((DiagramQuotient.projection R).app b)) :=
  OrdinaryQuotientPiZero.projection_surjective R b

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- Label preservation suffices; no smallness or higher-homotopy certificate is assumed.
example (b : Cᵒᵖ × C) :
    Function.Bijective (SSet.mapπ₀ ((DiagramQuotient.projection R).app b)) :=
  OrdinaryQuotientPiZero.projection_bijective Q R hR hcof hfib b

example (b : Cᵒᵖ × C) : SSet.π₀ ((DiagramQuotient.functor R).obj b) ≃
    (Q.obj b.1.unop ⟶ Q.obj b.2) :=
  OrdinaryQuotientPiZero.piZeroEquiv Q R hR hcof hfib b

variable (hsmall : ∀ b n, Small.{v} (Quotient (R.rel b n)))

example (b : Cᵒᵖ × C) : SSet.π₀ ((SmallDiagramQuotient.functor R hsmall).obj b) ≃
    (Q.obj b.1.unop ⟶ Q.obj b.2) :=
  OrdinaryQuotientPiZero.smallPiZeroEquiv Q R hR hcof hfib hsmall b

example {b c : Cᵒᵖ × C} (f : b ⟶ c)
    (z : SSet.π₀ ((SmallDiagramQuotient.functor R hsmall).obj b)) :
    OrdinaryQuotientPiZero.smallPiZeroEquiv Q R hR hcof hfib hsmall c
        (SSet.mapπ₀ ((SmallDiagramQuotient.functor R hsmall).map f) z) =
      Q.map f.1.unop ≫
        OrdinaryQuotientPiZero.smallPiZeroEquiv Q R hR hcof hfib hsmall b z ≫ Q.map f.2 :=
  OrdinaryQuotientPiZero.smallPiZeroEquiv_naturality Q R hR hcof hfib hsmall f z

example (b : Cᵒᵖ × C) (z : SSet.π₀ (OrdinaryResolutionBar.functor.obj b)) :
    OrdinaryQuotientPiZero.smallPiZeroEquiv Q R hR hcof hfib hsmall b
        (UniverseLiftPiZero.down _
          (SSet.mapπ₀ ((SmallDiagramQuotient.projection R hsmall).app b) z)) =
      OrdinaryBarPiZero.piZeroEquiv hcof hfib Q b z :=
  OrdinaryQuotientPiZero.smallProjection_factorization Q R hR hcof hfib hsmall b z
end Quotient

-- The canonical coarse kernel is an actual application, without higher preservation claims.
example {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
    [Q.IsLocalization (weakEquivalences C)] (b : Cᵒᵖ × C) :
    SSet.π₀ ((OrdinaryBarMappingClasses.coarseQuotient Q).obj b) ≃
      (Q.obj b.1.unop ⟶ Q.obj b.2) :=
  OrdinaryQuotientPiZero.smallPiZeroEquiv Q (OrdinaryBarMappingClasses.kernel Q)
    (fun b n {x y} h => (OrdinaryBarMappingClasses.kernel_iff Q b n x y).mp h)
    hcof hfib (OrdinaryBarMappingClasses.kernel_small Q) b

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftPiZero,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryQuotientPiZero]
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
    throwError "Missing ordinary quotient component modules"
  logInfo m!"Ordinary quotient component audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
