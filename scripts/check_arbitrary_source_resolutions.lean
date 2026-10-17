import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
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

-- Extend to every target using the ordinary localization; compare each value
-- with a genuine Kan mapping space and its ordinary Ho(C) hom set.
example {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
    [L.IsLocalization (weakEquivalences SSet.{v})] (X : Cᵒᵖ) (Y : C) :
    ∃ K : SSet.{v}, SSet.KanComplex K ∧
      Nonempty (((homotopyMapping hcof L (weakEquivalences C).Q).obj X).obj Y ≅ L.obj K) ∧
      Nonempty (SSet.π₀ K ≃ ((weakEquivalences C).Q.obj X.unop ⟶
        (weakEquivalences C).Q.obj Y)) :=
  homotopyMapping_has_representative hcof L (weakEquivalences C).Q X Y

-- Invariance in both original variables, including nonfibrant targets.
example {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
    [L.IsLocalization (weakEquivalences SSet.{v})]
    {X X' : Cᵒᵖ} (f : X ⟶ X') (hf : weakEquivalences C f.unop)
    {Y Y' : C} (g : Y ⟶ Y') (hg : weakEquivalences C g) :
    IsIso (((homotopyMapping hcof L (weakEquivalences C).Q).map f).app Y) ∧
      IsIso (((homotopyMapping hcof L (weakEquivalences C).Q).obj X).map g) :=
  ⟨homotopyMapping_map_source_isIso hcof L _ f hf Y,
    homotopyMapping_map_target_isIso hcof L _ X g hg⟩

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[`SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.LocalizedMappingBifunctor,

    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionCategory,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionCategoryHom,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionLiftIndependence,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.LocalizedResolutionHom]
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
