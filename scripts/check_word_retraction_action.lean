import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordContraction

universe u v
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

section Generic
variable {E B : SSet.{v}} (s : B ⟶ E) (p : E ⟶ B) (hs : s ≫ p = 𝟙 B)
  (H : SSet.Homotopy (𝟙 E) (p ≫ s))
  (hP : H.h ≫ p = fst E WordSegment.interval ≫ p)
  (hS : s ▷ WordSegment.interval ≫ H.h = fst B WordSegment.interval ≫ s)
open WordRetractionAction
example : E ⊗ WordSegment.obj ⟶ E := action s p hs H hP hS
example : E ◁ WordSegment.letter ≫ action s p hs H hP hS = H.h :=
  action_letter s p hs H hP hS
example {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (w : WordSegment.degree n) (x : E.obj n) :
    E.map θ (eval s p hs H hP hS n w x) =
      eval s p hs H hP hS m (WordSegment.degreeMap θ w) (E.map θ x) :=
  eval_naturality s p hs H hP hS θ w x
example : E ◁ WordSegment.mul ≫ action s p hs H hP hS =
    (α_ E WordSegment.obj WordSegment.obj).inv ≫
      action s p hs H hP hS ▷ WordSegment.obj ≫ action s p hs H hP hS :=
  action_mul s p hs H hP hS
example {T : SSet.{v}} (a : T ⟶ E) :
    lift a (WordSegment.unitAt T) ≫ action s p hs H hP hS = a :=
  action_unit s p hs H hP hS a
example {T : SSet.{v}} (a : T ⟶ E) :
    lift a (WordSegment.zeroAt T) ≫ action s p hs H hP hS = a ≫ p ≫ s :=
  action_zero s p hs H hP hS a
end Generic

section Actual
open SerrePositivity.HomotopyFunctionComplex
open OrdinaryBarRetractSystem OrdinaryBarWordContraction
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (b : Cᵒᵖ × C)
example : ambient hcof hfib b ⊗ WordSegment.obj ⟶ ambient hcof hfib b :=
  wordAction hcof hfib b
example : ambient hcof hfib b ◁ WordSegment.letter ≫ wordAction hcof hfib b =
    (contraction hcof hfib b).h := wordAction_letter hcof hfib b
example {T : SSet.{max u v}} (t w : T ⟶ WordSegment.obj) :
    ParameterComposition.comp (family hcof hfib b t) (family hcof hfib b w) =
      family hcof hfib b (lift t w ≫ WordSegment.mul) := family_mul hcof hfib b t w
example (T : SSet.{max u v}) : family hcof hfib b (WordSegment.unitAt T) =
    ParameterComposition.const T (𝟙 (ambient hcof hfib b)) := family_unit hcof hfib b T
example (T : SSet.{max u v}) : family hcof hfib b (WordSegment.zeroAt T) =
    ParameterComposition.const T (projection hcof hfib b ≫ section_ hcof hfib b) :=
  family_zero hcof hfib b T
example {T U : SSet.{max u v}} (t : T ⟶ WordSegment.obj) (j : U ⟶ T) :
    family hcof hfib b (j ≫ t) = ParameterComposition.substitute j (family hcof hfib b t) :=
  family_substitute hcof hfib b t j
end Actual

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[`SerrePositivity.HomotopicalAlgebra.Simplicial.RetractEndomorphisms,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordRetractionAction,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordContraction]
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
  unless modules.size == expected.size do throwError "Missing word action modules"
  logInfo m!"Word retraction action audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
