import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

section ActualRawCenters
variable (C : Type u) [Category.{v} C] [ModelCategory C]
open ResolutionArrowDiagram
-- Raw action transport needs no model structure on simplicial sets at all.
example {q r : Index C} (f : q ⟶ r) (Z : C) {T : SSet.{v}}
    (s : T ⟶ (fibers C).obj q)
    (t : T ⟶ (cosimplicialHom (target C r).resolution.obj).obj Z) :
    ResolutionArrowActionTransport.raw C r Z (s ≫ (fibers C).map f) t =
    ResolutionArrowActionTransport.raw C q Z s
      (t ≫ (cosimplicialHomMap f.hom.2.diagram).app Z) ≫
      ResolutionLiftPrecomposition.rawTargetMap f.hom.1.unop.map
        (FramedResolution.frameMap f.hom.1.unop) Z :=
  ResolutionArrowActionTransport.raw_transport C f Z s t
end ActualRawCenters

section IndependentIndexUniverses
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {D : Type uD} [Category.{vD} D] (H : D ⥤ ResolutionArrowDiagram.Index C)
  (K : D ⥤ SSet.{v})
  (a : NerveMovingParameter.System.{w, v} (NerveMovingParameter.lifted.{w} K)
    (H ⋙ ResolutionArrowDiagram.fibers C))
open NerveSmallAction
example {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (Z : C)
    (t : parameter K c ⟶ input C H c Z) :
    operatorParameter K c θ ≫ action C hcof hfib H K a c Z t =
    ResolutionArrowActionTransport.kan C hcof hfib (center C H (reindexChain c θ)) Z
      (prefixParameter K c θ ≫ NerveSmallFamilies.family K
        (H ⋙ ResolutionArrowDiagram.fibers C) a (reindexChain c θ))
      ((operatorParameter K c θ ≫ t) ≫ inputMap C H c θ Z) ≫
        outputMap C hcof hfib H c θ Z := operator C hcof hfib H K a c θ Z t
-- This formula also expresses genuine reindexing when the input reindexes.
example {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (Z : C)
    (t : parameter K c ⟶ input C H c Z)
    (t' : parameter K (reindexChain c θ) ⟶ input C H (reindexChain c θ) Z)
    (ht : (operatorParameter K c θ ≫ t) ≫ inputMap C H c θ Z = prefixParameter K c θ ≫ t') :
    operatorParameter K c θ ≫ action C hcof hfib H K a c Z t =
      (prefixParameter K c θ ≫ action C hcof hfib H K a (reindexChain c θ) Z t') ≫
        outputMap C hcof hfib H c θ Z := operator_of_input C hcof hfib H K a c θ Z t t' ht
example {n m l : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (σ : SimplexCategory.mk l ⟶ SimplexCategory.mk m) (Z : C) :
    inputMap C H c (σ ≫ θ) Z = inputMap C H c θ Z ≫ inputMap C H (reindexChain c θ) σ Z :=
  inputMap_comp C H c θ σ Z
example {n m l : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (σ : SimplexCategory.mk l ⟶ SimplexCategory.mk m) (Z : C) :
    outputMap C hcof hfib H c (σ ≫ θ) Z =
      outputMap C hcof hfib H (reindexChain c θ) σ Z ≫ outputMap C hcof hfib H c θ Z :=
  outputMap_comp C hcof hfib H c θ σ Z
end IndependentIndexUniverses

section SameMixedFacets
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
open ResolutionMixedDiagram ResolutionMixedSmallFamilies ResolutionMixedSmallAction
open ResolutionMixedActionOperators
example (side : Bool) (k : Fin 3) {n m : ℕ} (c : ComposableArrows (Index C) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (Z : C)
    (t : faceParameter C c ⟶ input C (c.obj (Fin.last n)) Z)
    (t' : faceParameter C (NerveSmallAction.reindexChain c θ) ⟶
      input C ((NerveSmallAction.reindexChain c θ).obj (Fin.last m)) Z)
    (ht : (NerveSmallAction.operatorParameter (smallIntervalParameter C) c θ ≫ t) ≫
      inputMap C c θ Z = NerveSmallAction.prefixParameter (smallIntervalParameter C) c θ ≫ t') :
    NerveSmallAction.operatorParameter (smallIntervalParameter C) c θ ≫
      faceAction C hcof hfib side k c Z t =
    (NerveSmallAction.prefixParameter (smallIntervalParameter C) c θ ≫
      faceAction C hcof hfib side k (NerveSmallAction.reindexChain c θ) Z t') ≫
        outputMap C hcof hfib c θ Z :=
  faceAction_operator_of_input C hcof hfib side k c θ Z t t' ht
example (k : Fin 3) {n m : ℕ} (c : ComposableArrows (Index C) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    ((smallFaceMap C k).app (c.obj 0) ▷ SSet.stdSimplex.obj (SimplexCategory.mk m)) ≫
      NerveSmallAction.operatorParameter (smallParameter C) c θ =
    NerveSmallAction.operatorParameter (smallIntervalParameter C) c θ ≫
      ((smallFaceMap C k).app (c.obj 0) ▷ SSet.stdSimplex.obj (SimplexCategory.mk n)) :=
  face_operator C k c θ
end SameMixedFacets

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowActionTransport,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowActionFunctors,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.NerveSmallAction,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedActionOperators]
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
    throwError "Some action operator modules were not audited"
  logInfo m!"Actual action operator audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
