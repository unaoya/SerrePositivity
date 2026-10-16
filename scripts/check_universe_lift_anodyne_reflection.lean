import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v uD vD u
noncomputable section
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.SimplicialModel SerrePositivity.SimplicialModel.AnodyneHomotopy

section WithoutAnyModel
variable {A B K : SSet.{v}} (i : A ⟶ B) (hi : SSet.anodyneExtensions i)
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))
example (f g : B ⟶ K) (h : SSet.Homotopy (i ≫ f) (i ≫ g)) :
    Nonempty (SSet.Homotopy f g) := KanHomotopyExtension.exists_homotopy i hi hK f g h
example : Function.Bijective (HomotopyClasses.pre i (K := K)) :=
  KanHomotopyClasses.pre_bijective i hi hK
example : HomotopyClasses.obj A K ≃
    HomotopyClasses.obj (UniverseLift.obj.{w} A) (UniverseLift.obj.{w} K) :=
  UniverseLift.homotopyClassEquiv A K
example (x : HomotopyClasses.obj B K) :
    UniverseLift.homotopyClassEquiv.{w} A K (HomotopyClasses.pre i x) =
      HomotopyClasses.pre (UniverseLift.map i)
        (UniverseLift.homotopyClassEquiv B K x) := UniverseLift.homotopyClassEquiv_pre i x
example : SSet.anodyneExtensions (UniverseLift.map.{w} i) ↔ SSet.anodyneExtensions i :=
  UniverseLift.anodyne_map_iff i
-- Neither endpoint of f is assumed Kan, and neither universe has a model structure.
example {X Y : SSet.{v}} (f : X ⟶ Y) :
    IsIso (anodyneQ.map (UniverseLift.map.{w} f)) ↔ IsIso (anodyneQ.map f) :=
  UniverseLift.anodyneQ_map_isIso_iff f
end WithoutAnyModel

section OriginalSmallModelOnly
open HomotopicalAlgebra
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
example {X Y : SSet.{v}} (f : X ⟶ Y) :
    weakEquivalences SSet.{v} f ↔ IsIso (anodyneQ.map (UniverseLift.map.{w} f)) :=
  UniverseLift.weakEquivalences_iff_lift_anodyneQ_isIso hcof hfib f
example {D : Type uD} [Category.{vD} D] {F G : D ⥤ SSet.{v}} (α : F ⟶ G) :
    (∀ d, weakEquivalences SSet.{v} (α.app d)) ↔
      IsIso (Functor.whiskerRight α (SSet.uliftFunctor.{w, v} ⋙ anodyneQ)) :=
  UniverseLift.natural_weakEquivalences_iff_lift_isIso hcof hfib α
-- The original arbitrary model source retains independent object and Hom universes.
example {C : Type u} [Category.{v} C] [ModelCategory C]
    {F G : (Cᵒᵖ × C) ⥤ SSet.{v}} (α : F ⟶ G)
    (hα : IsIso (Functor.whiskerRight α
      (SSet.uliftFunctor.{max u v, v} ⋙ anodyneQ))) :
    ∀ X, weakEquivalences SSet.{v} (α.app X) :=
  (UniverseLift.natural_weakEquivalences_iff_lift_isIso hcof hfib α).mpr hα
end OriginalSmallModelOnly

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanHomotopyExtension,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanHomotopyClasses,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftHomotopyClasses,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftAnodyneReflection]
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
    throwError "Some universe lift reflection modules were not audited"
  logInfo m!"Universe lift reflection audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
