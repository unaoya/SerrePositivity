import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v u u' v' t
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.SimplicialModel SerrePositivity.SimplicialModel.AnodyneHomotopy

section GeneralTargetProperty
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) (I : MorphismProperty C) (W : MorphismProperty D)
  [I.HasSmallObjectArgument.{t}] [PreservesColimitsOfSize.{t, t} F]
  [PreservesColimitsOfShape WalkingSpan F] [W.IsStableUnderRetracts]
  [W.IsStableUnderCobaseChange] [W.IsStableUnderCoproducts.{t}]
  [W.IsStableUnderTransfiniteComposition.{t}]
example (h : I ≤ W.inverseImage F) : I.rlp.llp ≤ W.inverseImage F :=
  SerrePositivity.ModelGeneration.generatedLeft_map F W I h
end GeneralTargetProperty

section NoModel
example {X Y : SSet.{v}} (f : X ⟶ Y) (hf : SSet.anodyneExtensions f) :
    SSet.anodyneExtensions (SSet.uliftFunctor.{w, v}.map f) :=
  UniverseLift.anodyne_map f hf
example {X Y : SSet.{v}} (f : X ⟶ Y) (hf : IsIso (anodyneQ.map f)) :
    IsIso (anodyneQ.map (SSet.uliftFunctor.{w, v}.map f)) :=
  UniverseLift.anodyneQ_map_isIso_of_small f hf
-- This also handles actual large relative-bar comparisons after a further lift.
example {D : Type u} [Category.{v'} D] {B : Type u'} [Category.{t} B]
    (p : D ⥤ B) (F : D ⥤ SSet.{v}) (d : D) :
    IsIso (anodyneQ.map (SSet.uliftFunctor.{w}.map
      ((BarConstruction.spanLeft p F).app d))) := by
  apply UniverseLift.anodyneQ_map_isIso_of_small
  exact inferInstanceAs (IsIso ((BarConstruction.spanLeftAnodyneIso p F).hom.app d))
end NoModel

section OnlyOriginalSmallModel
open HomotopicalAlgebra
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
example {X Y : SSet.{v}} (f : X ⟶ Y) (hf : weakEquivalences SSet.{v} f) :
    IsIso (anodyneQ.map (SSet.uliftFunctor.{w, v}.map f)) :=
  UniverseLift.anodyneQ_map_isIso_of_weakEquivalence hcof hfib f hf
end OnlyOriginalSmallModel

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Generated.FunctorClosure,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftAnodyne]
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
    throwError "Some universe lift anodyne modules were not audited"
  logInfo m!"Universe lift anodyne audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
