import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

-- No functorial factorizations, presentability, or enrichment on C.
example {C : Type u} [Category.{v} C] [ModelCategory C]
    (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) :
    ∃ g : X ⟶ Y, g.base = f := ⟨ResolutionObject.lift f, rfl⟩

example {C : Type u} [Category.{v} C] [ModelCategory C]
    (X : C) (Y : FibrantObject C) :
    SSet.KanComplex ((ResolutionObject.hom.obj
      (Opposite.op (ResolutionObject.ofObject X))).obj Y) :=
  ResolutionObject.hom_kanComplex _ _

-- Any ordinary localization, with independent object and Hom universes.
example {C : Type u} [Category.{v} C] [ModelCategory C]
    {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
    [Q.IsLocalization (weakEquivalences C)] (X : C) (Y : FibrantObject C) :
    SSet.π₀ ((ResolutionObject.hom.obj
      (Opposite.op (ResolutionObject.ofObject X))).obj Y) ≃ (Q.obj X ⟶ Q.obj Y.obj) :=
  ResolutionObject.piZeroEquiv Q _ _

-- Equality of arbitrary lifts in Ho(SSet), beyond pi zero.
example {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
    [L.IsLocalization (weakEquivalences SSet.{v})]
    {X X' : (ResolutionObject C)ᵒᵖ} (f g : X ⟶ X')
    (h : f.unop.base = g.unop.base) (Y : FibrantObject C) :
    L.map ((ResolutionObject.hom.map f).app Y) =
      L.map ((ResolutionObject.hom.map g).app Y) :=
  ResolutionObject.hom_map_eq_of_base_eq hcof L f g h Y

-- Strict source functor valued in Ho(SSet). Final SSet rectification remains.
example {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
    [L.IsLocalization (weakEquivalences SSet.{v})] :
    Cᵒᵖ ⥤ FibrantObject C ⥤ H := localizedResolutionHom hcof L

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCategory,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCategoryHom,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftIndependence,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.LocalizedResolutionHom]
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
  unless modules.size == expected.size do throwError "Some resolution mapping modules were not audited"
  logInfo m!"Arbitrary source resolution audit passed: {count} declarations in {modules.size} modules, standard axioms only."
