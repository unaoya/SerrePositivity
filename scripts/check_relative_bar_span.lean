import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v a b uD vD uB vB u
noncomputable section
open CategoryTheory
open SerrePositivity.SimplicialModel SerrePositivity.SimplicialModel.BarConstruction

section IndependentUniversesNoModelStructure
variable {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
  (p : D ⥤ B) (F : D ⥤ SSet.{v})
example : SSet.uliftFunctor.{a, v} ⋙ SSet.uliftFunctor.{b, max a v} ≅
    SSet.uliftFunctor.{max a b, v} := UniverseLift.iterationIso
example : relative (𝟭 D) F ⟶ F ⋙ SSet.uliftFunctor.{max uD vD, v} :=
  identityAugmentation F
example : relative (𝟭 D) F ⋙ SSet.uliftFunctor.{vB, max uD vD v} ⟶ p ⋙ relative p F :=
  unit p F
example {d e : D} (f : d ⟶ e) :
    (spanMiddle p F).map f ≫ (spanRight p F).app e =
      (spanRight p F).app d ≫ (p ⋙ relative p F).map f := (spanRight p F).naturality f
example {d e : D} (f : d ⟶ e) :
    (spanMiddle p F).map f ≫ (spanLeft p F).app e =
      (spanLeft p F).app d ≫ (F ⋙ SSet.uliftFunctor.{max uD vD vB, v}).map f :=
  (spanLeft p F).naturality f
example (d : D) : identitySection F d ≫ (identityAugmentation F).app d = 𝟙 _ :=
  identitySection_retract F d
example (d : D) : spanSection p F d ≫ (spanLeft p F).app d = 𝟙 _ :=
  spanSection_retract p F d
-- This is a full nerve homotopy at each fixed degree, not a claimed diagonal homotopy.
example (d : D) (n : SimplexCategoryᵒᵖ) :
    SSet.Homotopy
      (nerveMap (𝟭 (CostructuredArrow (elementProjection (𝟭 D) F n) d)))
      (nerveMap (identityCollapse F d n)) := identityNerveHomotopy F d n
example (d : D) (n : SimplexCategoryᵒᵖ)
    (c : ComposableArrows (CostructuredArrow (elementProjection (𝟭 D) F n) d) n.unop.len) :
    c ⋙ identityCollapse F d n =
      (Functor.const (Fin (n.unop.len + 1))).obj
        (identityPoint F d n ((F.map (c.obj 0).hom).app n (c.obj 0).left.val)) :=
  identityCollapse_chain F d n c
end IndependentUniversesNoModelStructure

section ActualPresentationSpan
open HomotopicalAlgebra SerrePositivity.HomotopyFunctionComplex
open ReplacementMapping
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
-- The original small mapping values are lifted explicitly; no large model is assumed.
example : auxiliaryMiddle (C := C) hcof hfib ⟶
    uncurried hcof hfib ⋙ SSet.uliftFunctor.{max u v, v} := auxiliaryLeft hcof hfib
example : auxiliaryMiddle (C := C) hcof hfib ⟶
    projection (C := C) ⋙ auxiliaryBar hcof hfib := auxiliaryRight hcof hfib
example (X : Index C) :
    auxiliarySection hcof hfib X ≫ (auxiliaryLeft hcof hfib).app X = 𝟙 _ :=
  auxiliarySection_retract hcof hfib X
end ActualPresentationSpan

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftIteration,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarUnit,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarIdentity,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarSpan,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ReplacementBarComparisonSpan]
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
    throwError "Some relative bar span modules were not audited"
  logInfo m!"Relative bar span audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
