import SerrePositivity.HomotopicalAlgebra.Localization.LeftProperTransfinite
import Lean.Util.CollectAxioms

noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Bousfield

variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SerrePositivity.SimplicialHomotopy.weakEquivalences)
  [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofB : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]



-- Exact original classes, arbitrary S (no smallness assumption), and independent universes.
example (S : MorphismProperty C) :
    (cofibrations C ⊓ localEquivalences.{v, u} (C := C) cof fib S).IsStableUnderCobaseChange ∧
    MorphismProperty.IsStableUnderTransfiniteComposition.{w}
      (cofibrations C ⊓ localEquivalences.{v, u} (C := C) cof fib S) :=
  localEquivalences_leftProperClosure cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB S

-- The actual generated class used by Smith recognition, with no assumed localized model.
example (S : MorphismProperty C) :
    (I.rlp.llp ⊓ localEquivalences.{v, u} (C := C) cof fib S).IsStableUnderCobaseChange ∧
    MorphismProperty.IsStableUnderTransfiniteComposition.{w}
      (I.rlp.llp ⊓ localEquivalences.{v, u} (C := C) cof fib S) :=
  localEquivalences_smithClosure cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB S

-- All well-orders, without cofinality restrictions or cofibrancy of the first object.
example (S : MorphismProperty C) (K : Type w) [LinearOrder K] [OrderBot K]
    [SuccOrder K] [WellFoundedLT K] (D : K ⥤ C) [D.IsWellOrderContinuous]
    (hstep : ∀ k, ¬IsMax k → (cofibrations C ⊓
      localEquivalences.{v, u} (C := C) cof fib S) (D.map (homOfLE (Order.le_succ k))))
    (c : Cocone D) (hc : IsColimit c) :
    localEquivalences.{v, u} (C := C) cof fib S (c.ι.app ⊥) :=
  localEquivalence_transfinite_cocone cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB S D hstep c hc

example (S : MorphismProperty C) (K : Type w) [LinearOrder K] [OrderBot K]
    [SuccOrder K] [WellFoundedLT K] {X Y : C} (f : X ⟶ Y)
    (d : MorphismProperty.TransfiniteCompositionOfShape
      (cofibrations C ⊓ localEquivalences.{v, u} (C := C) cof fib S) K f) :
    cofibrations C f ∧ localEquivalences.{v, u} (C := C) cof fib S f := by
  have := cof_localEquivalences_transfiniteStableOfShape cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB S K
  exact MorphismProperty.transfiniteCompositionsOfShape_le
    (cofibrations C ⊓ localEquivalences.{v, u} (C := C) cof fib S) K f ⟨d⟩

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Diagram.LimitPrefix,
    `SerrePositivity.HomotopicalAlgebra.Localization.ContinuousLocalEquivalences,
    `SerrePositivity.HomotopicalAlgebra.Localization.LeftProperTransfinite]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"Localization left proper closure audit passed: {count} declarations in {seen.size} modules."
