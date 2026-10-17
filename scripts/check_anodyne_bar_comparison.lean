import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v uD vD uB vB vH uH u
noncomputable section
open CategoryTheory
open SerrePositivity.SimplicialModel SerrePositivity.SimplicialModel.AnodyneHomotopy
open SerrePositivity.SimplicialModel.BarConstruction

section NoFullModelStructure
variable {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)
example (X : SSet.{v}) : SSet.anodyneExtensions (SSet.ι₀ (X := X)) := endpoint_zero_anodyne X
example (X : SSet.{v}) : SSet.anodyneExtensions (SSet.ι₁ (X := X)) := endpoint_one_anodyne X
example {X Y : SSet.{v}} {f g : X ⟶ Y} (h : SSet.Homotopy f g) : L.map f = L.map g :=
  map_homotopy_eq L hL h
example {X Y : SSet.{v}} (f : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ f = 𝟙 Y) (h : SSet.Homotopy (𝟙 X) (f ≫ s)) : L.obj X ≅ L.obj Y :=
  mapRetractionIso L hL f s hs h
example {X Y : SSet.{v}} (f : X ⟶ Y) (h : IsIso (anodyneQ.map f)) : IsIso (L.map f) :=
  map_isIso_of_anodyneQ_isIso L hL f h
end NoFullModelStructure

section IndependentIndexUniverses
variable {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
  (p : D ⥤ B) (F : D ⥤ SSet.{v})
example : spanMiddle p F ⋙ anodyneQ ≅
    (F ⋙ SSet.uliftFunctor.{max uD vD vB, v}) ⋙ anodyneQ := spanLeftAnodyneIso p F
example (d : D) :
    (spanLeftAnodyneIso p F).hom.app d = anodyneQ.map ((spanLeft p F).app d) := rfl
end IndependentIndexUniverses

section OriginalSmallWeakClass
open HomotopicalAlgebra
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
example {X Y : SSet.{v}} (f : X ⟶ Y) :
    weakEquivalences SSet.{v} f ↔ IsIso (anodyneQ.map f) :=
  weakEquivalences_iff_anodyneQ_isIso hcof hfib f
example {X Y : SSet.{v}} (f : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ f = 𝟙 Y) (h : SSet.Homotopy (𝟙 X) (f ≫ s)) :
    weakEquivalences SSet.{v} f := homotopy_retraction_weakEquivalence hcof hfib f s hs h
-- A genuinely v-small auxiliary index gives an actual model weak equivalence.
example {D : Type v} [Category.{v} D] {B : Type uB} [Category.{v} B]
    (p : D ⥤ B) (F : D ⥤ SSet.{v}) (d : D) :
    weakEquivalences SSet.{v} ((spanLeft p F).app d) :=
  homotopy_retraction_weakEquivalence hcof hfib ((spanLeft p F).app d) (spanSection p F d)
    (spanSection_retract p F d) (spanLeftHomotopy p F d)
end OriginalSmallWeakClass

section ActualArbitraryModelSource
open HomotopicalAlgebra SerrePositivity.HomotopyFunctionComplex ReplacementMapping
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
-- u and v stay independent, and no model on SSet[max(u,v)] is assumed.
example : auxiliaryMiddle (C := C) hcof hfib ⋙ anodyneQ ≅
    (uncurried hcof hfib ⋙ SSet.uliftFunctor.{max u v, v}) ⋙ anodyneQ :=
  auxiliaryLeftAnodyneIso hcof hfib
example (X : Index C) :
    (auxiliaryLeftAnodyneIso hcof hfib).hom.app X =
      anodyneQ.map ((auxiliaryLeft hcof hfib).app X) := auxiliaryLeftAnodyneIso_hom_app hcof hfib X
end ActualArbitraryModelSource

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneIntervalEndpoints,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneModelDetection,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarAnodyneComparison,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ReplacementBarAnodyneComparison]
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
    throwError "Some anodyne bar comparison modules were not audited"
  logInfo m!"Anodyne bar comparison audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
