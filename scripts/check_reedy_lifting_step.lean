import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LiftingStep
import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexFinite
import Lean.Util.CollectAxioms

universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J) {C : Type u'} [Category.{v'} C]
  [HasColimitsOfShape (LatchingIndex r j) C] [HasLimitsOfShape (MatchingIndex r j) C]
  [HasPushouts C] [HasPullbacks C]
  {A B X Y : J ⥤ C} {i : A ⟶ B} {p : X ⟶ Y} {a : A ⟶ X} {b : B ⟶ Y}
  (sq : CommSq a i p b)
  (ℓ : lowerInclusion r (r.deg j) ⋙ B ⟶ lowerInclusion r (r.deg j) ⋙ X)
  (hi : Functor.whiskerLeft (lowerInclusion r (r.deg j)) i ≫ ℓ =
    Functor.whiskerLeft (lowerInclusion r (r.deg j)) a)
  (hp : ℓ ≫ Functor.whiskerLeft (lowerInclusion r (r.deg j)) p =
    Functor.whiskerLeft (lowerInclusion r (r.deg j)) b)

example : CommSq (LiftingStep.top r j ℓ hi) (relativeLatchingMap r j i)
    (relativeMatchingMap r j p) (LiftingStep.bottom r j ℓ hp) :=
  LiftingStep.square r j ℓ hi hp sq

example [HasLiftingProperty (relativeLatchingMap r j i) (relativeMatchingMap r j p)] :
    ∃ l : B.obj j ⟶ X.obj j,
      i.app j ≫ l = a.app j ∧ l ≫ p.app j = b.app j ∧
      (∀ f : LatchingIndex r j,
        B.map f.obj.hom ≫ l = ℓ.app ((latchingSourceLower r j).obj f) ≫ X.map f.obj.hom) ∧
      (∀ g : MatchingIndex r j,
        l ≫ X.map g.obj.hom = B.map g.obj.hom ≫ ℓ.app ((matchingTargetLower r j).obj g)) :=
  ⟨LiftingStep.component r j sq ℓ hi hp, LiftingStep.component_fac_left r j sq ℓ hi hp,
    LiftingStep.component_fac_right r j sq ℓ hi hp, LiftingStep.incoming r j sq ℓ hi hp,
    LiftingStep.outgoing r j sq ℓ hi hp⟩

example {F G : J ⥤ C} (τ : F ⟶ G) :
    latchingExtension r j (Functor.whiskerLeft (lowerInclusion r (r.deg j)) τ) =
      (latchingComparison r j).app F ≫ τ.app j := latchingExtension_restrict r j τ

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LowerTransformationNaturality,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LiftingStep]
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
  if modules.size != expected.size then throwError "Not all Reedy lifting-step modules were audited"
  logInfo m!"Reedy lifting step audit passed: {count} declarations in 2 modules, standard axioms only."
