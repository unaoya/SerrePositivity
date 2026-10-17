import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u vS uS vH uH vD uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.ModelReplacement SerrePositivity.HomotopyFunctionComplex

section OrdinaryFactorizationOnly
variable {C : Type u} [Category.{v} C] [ModelCategory C]
-- The base object need not be fibrant. No functorial factorization is supplied.
example (X : C) : (FibrantReplacementObject.ofObject X).base = X := rfl
example : (FibrantReplacementObject.projection (C := C)).Full := inferInstance
example : 𝟭 (FibrantReplacementObject C) ⟶
    FibrantReplacementObject.fibrantTargets ⋙ FibrantReplacementObject.fromFibrant :=
  FibrantReplacementObject.toIdentityPresentation
example {X Y : FibrantReplacementObject C} (f : X.base ⟶ Y.base) :
    (FibrantReplacementObject.liftBase (X := X) (Y := Y) f).base = f := rfl
example {X Y : FibrantReplacementObject C} (f : X ⟶ Y) :
    weakEquivalences C f.map ↔ weakEquivalences C f.base :=
  FibrantReplacementObject.map_weakEquivalence_iff f
variable {D : Type uD} [Category.{vD} D] (F : FibrantObject C ⥤ D)
  (hF : (weakEquivalences (FibrantObject C)).IsInvertedBy F)
example {X Y : FibrantReplacementObject C} (f g : X ⟶ Y) (h : f.base = g.base) :
    F.map (FibrantReplacementObject.fibrantTargets.map f) =
      F.map (FibrantReplacementObject.fibrantTargets.map g) :=
  FibrantReplacementObject.homotopical_map_eq_of_base_eq (weakEquivalences C).Q F hF f g h
end OrdinaryFactorizationOnly

section SmallBothVariableMapping
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
open ReplacementMapping
example : (FramedResolution C)ᵒᵖ ⥤ FibrantReplacementObject C ⥤ SSet.{v} := hom hcof hfib
example : hom (C := C) hcof hfib ⋙
    (Functor.whiskeringLeft (FibrantObject C) (FibrantReplacementObject C) SSet.{v}).obj
      FibrantReplacementObject.fromFibrant = FramedResolution.fibrantHom hcof hfib :=
  fibrant_restriction hcof hfib
-- Both underlying objects are arbitrary: only their actual presentations are resolved.
example (X Y : C) :
    SSet.KanComplex ((uncurried hcof hfib).obj (ofBase (Opposite.op X, Y))) :=
  kanComplex hcof hfib (Opposite.op (FramedResolution.ofObject X))
    (FibrantReplacementObject.ofObject Y)
example (X : (FramedResolution C)ᵒᵖ) (Y : FibrantReplacementObject C) :
    weakEquivalences SSet.{v} (((comparison hcof hfib).app X).app Y) :=
  comparison_weakEquivalence hcof hfib X Y
example {X X' : (FramedResolution C)ᵒᵖ} (f : X ⟶ X')
    (hf : weakEquivalences C f.unop.map.base) (Y : FibrantReplacementObject C) :
    weakEquivalences SSet.{v} (((hom hcof hfib).map f).app Y) :=
  source_weakEquivalence hcof hfib f hf Y
example (X : (FramedResolution C)ᵒᵖ) {Y Y' : FibrantReplacementObject C}
    (f : Y ⟶ Y') (hf : weakEquivalences C f.base) :
    weakEquivalences SSet.{v} (((hom hcof hfib).obj X).map f) :=
  target_weakEquivalence hcof hfib X f hf
example {X Y Z : Index C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (uncurried hcof hfib).map (f ≫ g) =
      (uncurried hcof hfib).map f ≫ (uncurried hcof hfib).map g :=
  (uncurried hcof hfib).map_comp f g
variable {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]
example (X Y : C) :
    SSet.π₀ ((uncurried hcof hfib).obj (ofBase (Opposite.op X, Y))) ≃
      (Q.obj X ⟶ Q.obj Y) :=
  piZeroEquiv hcof hfib Q (Opposite.op (FramedResolution.ofObject X))
    (FibrantReplacementObject.ofObject Y)
example {X X' : (FramedResolution C)ᵒᵖ} (f : X ⟶ X')
    (Y : FibrantReplacementObject C) (z : SSet.π₀ (((hom hcof hfib).obj X).obj Y)) :
    piZeroEquiv hcof hfib Q X' Y (SSet.mapπ₀ (((hom hcof hfib).map f).app Y) z) =
      Q.map f.unop.map.base ≫ piZeroEquiv hcof hfib Q X Y z :=
  piZero_naturality_source hcof hfib Q f Y z
example (X : (FramedResolution C)ᵒᵖ) {Y Y' : FibrantReplacementObject C} (f : Y ⟶ Y')
    (z : SSet.π₀ (((hom hcof hfib).obj X).obj Y)) :
    piZeroEquiv hcof hfib Q X Y' (SSet.mapπ₀ (((hom hcof hfib).obj X).map f) z) =
      piZeroEquiv hcof hfib Q X Y z ≫ Q.map f.base :=
  piZero_naturality_target hcof hfib Q X f z
variable {S : Type uS} [Category.{vS} S] (L : SSet.{v} ⥤ S)
  [L.IsLocalization (weakEquivalences SSet.{v})]
example {X Y : Index C} (f g : X ⟶ Y)
    (hs : f.1.unop.map.base = g.1.unop.map.base) (ht : f.2.base = g.2.base) :
    L.map ((uncurried hcof hfib).map f) = L.map ((uncurried hcof hfib).map g) :=
  localized_uncurried_map_eq hcof hfib L f g hs ht
example : projection (C := C) ⋙ descended hcof hfib L ≅ uncurried hcof hfib ⋙ L :=
  descentComparisonIso hcof hfib L
example (X : Index C) :
    weakEquivalences SSet.{v} (presentationMap hcof hfib X) :=
  presentationMap_weakEquivalence hcof hfib X
example (X : Index C) :
    (descentComparisonIso hcof hfib L).hom.app X = L.map (presentationMap hcof hfib X) := rfl
example {X Y : Cᵒᵖ × C} (f : X ⟶ Y)
    (hs : weakEquivalences C f.1.unop) (ht : weakEquivalences C f.2) :
    IsIso ((descended hcof hfib L).map f) := descended_map_isIso hcof hfib L f hs ht
end SmallBothVariableMapping

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Replacement.FibrantCategory,
    `SerrePositivity.HomotopicalAlgebra.Replacement.FibrantLocalization,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ReplacementMappingBifunctor,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ReplacementMappingLocalization,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ReplacementMappingDescent]
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
    throwError "Some replacement mapping modules were not audited"
  logInfo m!"Replacement mapping descent audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
