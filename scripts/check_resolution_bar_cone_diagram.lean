import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)
  (a : NerveFirstChoice.System (ResolutionBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (ResolutionBarCenters.rightChoices R))

-- Whole natural transformations on the actual bar simplex category, with independent u and v.
example : ResolutionBarConeDiagram.leftSource R ⟶ ResolutionBarConeDiagram.leftTarget R :=
  ResolutionBarConeDiagram.left R a
example : ResolutionBarConeDiagram.rightSource R ⟶ ResolutionBarConeDiagram.rightTarget R :=
  ResolutionBarConeDiagram.right R b

example {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t) :
    (ResolutionBarConeDiagram.leftSource R).map f ≫ (ResolutionBarConeDiagram.left R a).app t =
      (ResolutionBarConeDiagram.left R a).app s ≫ (ResolutionBarConeDiagram.leftTarget R).map f :=
  (ResolutionBarConeDiagram.left R a).naturality f

example {s t : ResolutionBarConeDiagram.Index R} (f : s ⟶ t) :
    (ResolutionBarConeDiagram.rightSource R).map f ≫ (ResolutionBarConeDiagram.right R b).app t =
      (ResolutionBarConeDiagram.right R b).app s ≫ (ResolutionBarConeDiagram.rightTarget R).map f :=
  (ResolutionBarConeDiagram.right R b).naturality f

-- The prefix is the original comma chain map, and the row degree changes by the same operator.
example {n m : ℕ} (c : ComposableArrows (ResolutionBarCenters.Comma R) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    ResolutionFrameRows.rowMap R.1.unop.inner θ ≫ ResolutionBarRowOperators.left R a c =
      ResolutionBarRowOperators.left R a ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
        (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))).left.1.unop.map :=
  ResolutionBarRowOperators.left_operator R a c θ

example {n m : ℕ} (c : ComposableArrows (ResolutionBarCenters.Comma R) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    ResolutionFrameRows.rowMap R.2.unop.inner θ ≫ ResolutionBarRowOperators.right R b c =
      ResolutionBarRowOperators.right R b ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
        (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))).left.2.unop.map :=
  ResolutionBarRowOperators.right_operator R b c θ

-- Both original simplex cone maps are retained, as full resolution maps.
example (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n) :
    (ResolutionBarConeDiagram.left R a).app (op ((ResolutionBarEvaluation.bar R).elementsMk n c)) =
      ResolutionBarSimplexCone.left R a n c := ResolutionBarConeDiagram.left_recovery R a n c
example (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n) :
    (ResolutionBarConeDiagram.right R b).app (op ((ResolutionBarEvaluation.bar R).elementsMk n c)) =
      ResolutionBarSimplexCone.right R b n c := ResolutionBarConeDiagram.right_recovery R b n c

-- Actual selected systems need only the original small model structure.
example [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _) :
    ResolutionBarConeDiagram.leftSource R ⟶ ResolutionBarConeDiagram.leftTarget R :=
  ResolutionBarConeDiagram.left R (ResolutionBarCenters.leftSystem R hcof)

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionCenterRowLaws,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionBarRowDiagram,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionBarRowOperators,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionBarConeDiagram]
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
    throwError "Some resolution bar cone diagram modules were not audited"
  logInfo m!"Resolution bar cone diagram audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
