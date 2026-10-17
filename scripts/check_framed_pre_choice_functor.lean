import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u vD uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

section GeneralDiagram
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})
  {A K : SSet.{v}} (i : A ⟶ K) (b : (Functor.const D).obj A ⟶ F)
  (a : (Functor.const D).obj K ⟶ F) (ha : ∀ X, i ≫ a.app X = b.app X)

-- General diagram, independent object/Hom universes, no model or monicity assumptions.
example : D ⥤ SSet.{v} := RelativeChoiceFunctor.functor F i b
example : RelativeChoiceFunctor.point F i b a ha ≫ RelativeChoiceFunctor.projection F i b = 𝟙 _ :=
  RelativeChoiceFunctor.point_projection F i b a ha
end GeneralDiagram

section ActualFrames
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {Y : FramedResolution C} (W : ResolutionObject C) (g : Y.inner.base ⟶ W.base)

-- The underlying fibers form a strict diagram before supplying any simplicial model.
example : (Over Y)ᵒᵖ ⥤ SSet.{v} := FramedPreChoiceFunctor.fibers W g
example {a b c : Over Y} (k : a ⟶ b) (l : b ⟶ c) :
    FramedPreChoiceFunctor.fiberMap W g (k ≫ l) =
      FramedPreChoiceFunctor.fiberMap W g l ≫ FramedPreChoiceFunctor.fiberMap W g k :=
  FramedPreChoiceFunctor.fiberMap_compose W g k l

-- The context map is the old actual source transport, with its base equality explicit.
example {a b : Over Y} (k : a ⟶ b) : FramedPreChoiceFunctor.fiberMap W g k =
    ResolutionLiftPrecomposition.map a.left.inner b.left.inner W k.left.map
        (b.hom.map.base ≫ g) (FramedResolution.frameMap k.left) ≫
      ResolutionLiftSpace.baseChange (FramedPreChoiceFunctor.base_eq W g k) :=
  FramedPreChoiceFunctor.fiberMap_existing W g k
end ActualFrames

section PrecomparisonSpaces
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {Y : FramedResolution C} (W : ResolutionObject C) (g : Y.inner.base ⟶ W.base)

example : (Over Y)ᵒᵖ ⥤ SSet.{v} := FramedPreChoiceFunctor.functor W g hcof
example (a : (Over Y)ᵒᵖ) : (FramedPreChoiceFunctor.functor W g hcof).obj a =
    CoherentLiftRelative.preChoiceSpace a.unop.left.inner Y.inner W a.unop.hom.map g :=
  FramedPreChoiceFunctor.functor_obj W g hcof a
example (a : (Over Y)ᵒᵖ) : (FramedPreChoiceFunctor.point W g hcof).app a =
    CoherentLiftRelative.preLeftPoint hcof a.unop.left.inner Y.inner W a.unop.hom.map g
      (FramedResolution.frameMap a.unop.hom) := FramedPreChoiceFunctor.point_component W g hcof a
example {a b c : (Over Y)ᵒᵖ} (k : a ⟶ b) (l : b ⟶ c) :
    (FramedPreChoiceFunctor.functor W g hcof).map (k ≫ l) =
      (FramedPreChoiceFunctor.functor W g hcof).map k ≫
        (FramedPreChoiceFunctor.functor W g hcof).map l :=
  (FramedPreChoiceFunctor.functor W g hcof).map_comp k l
example : FramedPreChoiceFunctor.point W g hcof ≫ FramedPreChoiceFunctor.projection W g hcof = 𝟙 _ :=
  FramedPreChoiceFunctor.point_projection W g hcof
example (a : (Over Y)ᵒᵖ) :
    trivialFibrations SSet.{v} ((FramedPreChoiceFunctor.projection W g hcof).app a) :=
  FramedPreChoiceFunctor.projection_trivialFibration W g hcof hfib a
example (a : (Over Y)ᵒᵖ) : weakEquivalences SSet.{v} ((FramedPreChoiceFunctor.point W g hcof).app a) :=
  FramedPreChoiceFunctor.point_weakEquivalence W g hcof hfib a
end PrecomparisonSpaces

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceFunctor,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.FramedPreChoiceFunctor]
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
    throwError "Some framed precomposition modules were not audited"
  logInfo m!"Framed precomposition choice audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
