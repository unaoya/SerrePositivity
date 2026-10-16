import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

section ArbitrarySource
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- Postcomposition is an actual map of lift spaces over the composite base map.
-- At strict vertices it is exactly the original resolution composition.
example {X Y W : ResolutionObject C} (k : X ⟶ Y) (g : Y ⟶ W) :
    ResolutionLiftSpace.ofLift k ≫ ResolutionLiftPostcomposition.map X Y W k.base g =
      ResolutionLiftSpace.ofLift (k ≫ g) := ResolutionLiftPostcomposition.ofLift k g

-- An entire coherent comparison simplex can be postcomposed, and its action
-- is exactly precomposition of the original Hom by the strict target map.
example (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) (Z : C) {n : ℕ}
    (a : Fin (n + 1) → CoherentLiftTuples.StrictLift X Y f)
    (t : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶
      (cosimplicialHom W.resolution.obj).obj Z) :
    KanLiftAction.parameterized hcof hfib X W (f ≫ g.base) Z
        (CoherentLiftTuples.simplex hcof X Y f a ≫
          ResolutionLiftPostcomposition.map X Y W f g) t =
      KanLiftAction.parameterized hcof hfib X Y f Z (CoherentLiftTuples.simplex hcof X Y f a)
        (t ≫ (cosimplicialHomMap g.diagram).app Z) :=
  ResolutionLiftPostcomposition.kan_action hcof hfib X Y W f g Z _ t

-- Extend prescribed data first, and postcompose without losing its boundary.
-- All the resulting actions agree, simultaneously for all Z and t.
example (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W)
    {K L : SSet.{v}} (i : K ⟶ L) [Mono i] (b : K ⟶ ResolutionLiftSpace.obj X Y f) :
    ∃ e : L ⟶ ResolutionLiftSpace.obj X Y f,
      i ≫ (e ≫ ResolutionLiftPostcomposition.map X Y W f g) =
        b ≫ ResolutionLiftPostcomposition.map X Y W f g ∧
      ∀ (Z : C) (t : L ⟶ (cosimplicialHom W.resolution.obj).obj Z),
        KanLiftAction.parameterized hcof hfib X W (f ≫ g.base) Z
            (e ≫ ResolutionLiftPostcomposition.map X Y W f g) t =
          KanLiftAction.parameterized hcof hfib X Y f Z e
            (t ≫ (cosimplicialHomMap g.diagram).app Z) := by
  obtain ⟨e, he⟩ := ResolutionLiftSpace.extension hcof X Y f i b
  exact ⟨e, ResolutionLiftPostcomposition.boundary X Y W f g i b e he,
    fun Z t => ResolutionLiftPostcomposition.kan_action hcof hfib X Y W f g Z e t⟩

end ArbitrarySource

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalHomComposition,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPostcomposition]
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
  unless modules.size == expected.size do throwError "Some postcomposition modules were not audited"
  logInfo m!"Lift postcomposition audit passed: {count} declarations in {modules.size} modules, \
    standard axioms only."
