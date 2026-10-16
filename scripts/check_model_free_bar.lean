import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v uD vD uB vB u
noncomputable section
open CategoryTheory
open SerrePositivity.SimplicialModel.BarConstruction

section NoModelStructure
variable {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
  (p : D ⥤ B) (F : D ⥤ SSet.{v})
example : (D ⥤ SSet.{v}) ⥤ SSet.{max uD vD v} := functor D
example (n : SimplexCategoryᵒᵖ) :
    ((functor D).obj F).obj n =
      ComposableArrows ((F.flip.obj n).Elements) n.unop.len := obj_degree D F n
example {G H : D ⥤ SSet.{v}} (a : F ⟶ G) (b : G ⟶ H) :
    (functor D).map (a ≫ b) = (functor D).map a ≫ (functor D).map b :=
  (functor D).map_comp a b
example {K : SSet.{v}} (a : F ⟶ (Functor.const D).obj K) :
    (functor D).obj F ⟶ SSet.uliftFunctor.{max uD vD, v}.obj K := augmentation a
example : B ⥤ SSet.{max uD vD v vB} := relative p F
example (b : B) (n : SimplexCategoryᵒᵖ) :
    ((relative p F).obj b).obj n =
      ComposableArrows (CostructuredArrow (elementProjection p F n) b) n.unop.len :=
  relative_obj_degree p F b n
example {b c d : B} (f : b ⟶ c) (g : c ⟶ d) :
    (relative p F).map (f ≫ g) = (relative p F).map f ≫ (relative p F).map g :=
  (relative p F).map_comp f g
example {G : B ⥤ SSet.{v}} (a : F ⟶ p ⋙ G) :
    relative p F ⟶ G ⋙ SSet.uliftFunctor.{max uD vD vB, v} := relativeAugmentation p F a
example {G : B ⥤ SSet.{v}} (a : F ⟶ p ⋙ G) {b c : B} (f : b ⟶ c) :
    (relative p F).map f ≫ (relativeAugmentation p F a).app c =
      (relativeAugmentation p F a).app b ≫
        (G ⋙ SSet.uliftFunctor.{max uD vD vB, v}).map f :=
  (relativeAugmentation p F a).naturality f
-- The small input values do not by themselves bound the raw bar's size.
example : Function.Injective (indexVertex.{v} D) := indexVertex_injective D
example : ¬ Small.{v} (((functor (Codiscrete (Type v))).obj
    (pointDiagram.{v} (Codiscrete (Type v)))).obj (Opposite.op (SimplexCategory.mk 0))) :=
  point_bar_not_small
end NoModelStructure

section ActualReplacementDiagram
open HomotopicalAlgebra SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
-- No model structure on SSet.{max u v} occurs among the hypotheses.
example : (Cᵒᵖ × C) ⥤ SSet.{max u v} := ReplacementMapping.auxiliaryBar hcof hfib
example {X Y Z : Cᵒᵖ × C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (ReplacementMapping.auxiliaryBar hcof hfib).map (f ≫ g) =
      (ReplacementMapping.auxiliaryBar hcof hfib).map f ≫
        (ReplacementMapping.auxiliaryBar hcof hfib).map g :=
  (ReplacementMapping.auxiliaryBar hcof hfib).map_comp f g
end ActualReplacementDiagram

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.BarConstruction,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.BarAugmentation,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarConstruction,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarAugmentation,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.BarSize,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarCandidate]
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
    throwError "Some model-free bar modules were not audited"
  logInfo m!"Model-free bar audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
