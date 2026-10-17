import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe w v uD vD uB vB u
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel SerrePositivity.SimplicialModel.BarConstruction

section NoModelStructure
variable {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
  (p : D ⥤ B) (F : D ⥤ SSet.{v})
example (d : D) {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    contractionInterval F d n ⋙ identityLevelMap F d θ =
      (𝟭 (Fin 2)).prod (identityLevelMap F d θ) ⋙ contractionInterval F d m :=
  contractionInterval_operator F d θ
-- The interval is a morphism of actual diagonal simplicial sets, with all operators.
example (d : D) : SSet.Homotopy (𝟙 ((relative (𝟭 D) F).obj d))
    ((identityAugmentation F).app d ≫ identitySection F d) := identityDiagonalHomotopy F d
example (d : D) : SSet.ι₀ ≫ identityHomotopyMap F d = 𝟙 _ := identityHomotopyMap_zero F d
example (d : D) : SSet.ι₁ ≫ identityHomotopyMap F d =
    (identityAugmentation F).app d ≫ identitySection F d := identityHomotopyMap_one F d
example {K P : SSet.{v}} {f g : K ⟶ P} (H : SSet.Homotopy f g) :
    SSet.Homotopy (UniverseLift.map.{w} f) (UniverseLift.map.{w} g) := UniverseLift.homotopy H
-- Both homotopy inverse equations concern the same span maps and the same section.
example (d : D) : spanSection p F d ≫ (spanLeft p F).app d = 𝟙 _ :=
  spanSection_retract p F d
example (d : D) : SSet.Homotopy (𝟙 ((spanMiddle p F).obj d))
    ((spanLeft p F).app d ≫ spanSection p F d) := spanLeftHomotopy p F d
end NoModelStructure

section ActualMappingSpan
open HomotopicalAlgebra SerrePositivity.HomotopyFunctionComplex
open ReplacementMapping
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
-- No model on SSet.{max u v} and no functorial source factorization is supplied.
example (X : Index C) : SSet.Homotopy (𝟙 ((auxiliaryMiddle hcof hfib).obj X))
    ((auxiliaryLeft hcof hfib).app X ≫ auxiliarySection hcof hfib X) :=
  auxiliaryLeftHomotopy hcof hfib X
example (X : Index C) :
    ∃ s : SSet.uliftFunctor.{max u v, v}.obj ((uncurried hcof hfib).obj X) ⟶
      (auxiliaryMiddle hcof hfib).obj X,
      s ≫ (auxiliaryLeft hcof hfib).app X = 𝟙 _ ∧
        Nonempty (SSet.Homotopy (𝟙 _) ((auxiliaryLeft hcof hfib).app X ≫ s)) :=
  auxiliaryLeft_has_homotopyInverse hcof hfib X
end ActualMappingSpan

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarContractionOperators,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarDiagonalContraction,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftHomotopy,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarSpanContraction,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ReplacementBarLeftContraction]
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
    throwError "Some diagonal contraction modules were not audited"
  logInfo m!"Relative bar diagonal contraction audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
