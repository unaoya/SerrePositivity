import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] [ModelCategory C]

-- A higher lift supplies a full map from the actual row resolution, over the given base map.
example (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) {T : SSet.{v}}
    (s : T ⟶ ResolutionLiftSpace.obj X Y f) (n : SimplexCategoryᵒᵖ) (x : T.obj n) :
    ResolutionFrameRows.row X n.unop ⟶ Y := ResolutionLiftRows.map X Y f s n x

example (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) {T : SSet.{v}}
    (s : T ⟶ ResolutionLiftSpace.obj X Y f) {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (x : T.obj n) :
    ResolutionFrameRows.rowMap X θ.unop ≫ ResolutionLiftRows.map X Y f s n x =
      ResolutionLiftRows.map X Y f s m (T.map θ x) :=
  ResolutionLiftRows.naturality X Y f s θ x

-- All changing centers transport the full resolution map, including both endpoint maps.
example {q r : ResolutionArrowDiagram.Index C} (k : q ⟶ r) {T : SSet.{v}}
    (s : T ⟶ (ResolutionArrowDiagram.fibers C).obj q) (n : SimplexCategoryᵒᵖ) (x : T.obj n) :
    ResolutionCenterRowLifts.map C r (s ≫ (ResolutionArrowDiagram.fibers C).map k) n x =
      (ResolutionFrameRowFunctor.component k.hom.1.unop n.unop ≫
        ResolutionCenterRowLifts.map C q s n x) ≫ k.hom.2 :=
  ResolutionCenterRowLifts.transport C k s n x

variable (R : RightResolutionMapping.Index C)
  (a : NerveFirstChoice.System (ResolutionBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (ResolutionBarCenters.rightChoices R))

-- The exact evaluation label occurs at the target of an actual arrow in the original bar degree.
example (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n) :
    c.obj 0 ⟶ ResolutionBarSimplexCone.element R a b n c :=
  ResolutionBarSimplexCone.elementArrow R a b n c

example (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n) :
    ((MixedBiresolutionComparison.functor (C := C)).map
        (ResolutionBarSimplexCone.arrow R a b n c)).app n (c.obj 0).left.val =
      ((ResolutionBarEvaluation.evaluation R a b).app n c).down :=
  ResolutionBarSimplexCone.arrow_label R a b n c

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

example (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n)
    (hs : weakEquivalences C (c.obj 0).hom.1.unop)
    (ht : weakEquivalences Cᵒᵖ (c.obj 0).hom.2.op) :
    weakEquivalences SSet.{v} ((MixedBiresolutionComparison.functor (C := C)).map
      (ResolutionBarSimplexCone.arrow R a b n c)) :=
  ResolutionBarSimplexCone.arrow_raw_weakEquivalence R a b hcof hfib n c hs ht

example (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n) :
    c.obj 0 ⟶ ResolutionBarSimplexCone.element R
      (ResolutionBarCenters.leftSystem R hcof) (ResolutionBarCenters.rightSystem R hcof) n c :=
  ResolutionBarSimplexCone.elementArrow R _ _ n c

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionLiftRows,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionCenterRowLifts,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionBarSimplexCone]
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
    throwError "Some resolution bar simplex cone modules were not audited"
  logInfo m!"Resolution bar simplex cone audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
