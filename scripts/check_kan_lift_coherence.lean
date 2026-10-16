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

-- A single interval chosen before Z supplies a target-natural action family,
-- with exact endpoints, for an arbitrary strict lift. No source factorization
-- functor, local presentability, or enrichment is an input.
example {X Y : ResolutionObject C} (f : X ⟶ Y) :
    ∃ H : ∀ Z : C, SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⨯
        (cosimplicialHom Y.resolution.obj).obj Z ⟶ KanLiftAction.target hcof hfib X Z,
      (∀ Z : C,
        prod.map (SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2))) (𝟙 _) ≫ H Z =
          prod.snd ≫ KanLiftCoherence.chosenMap X Y f.base Z ≫
            KanLiftAction.comparison hcof hfib X Z ∧
        prod.map (SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2))) (𝟙 _) ≫ H Z =
          prod.snd ≫ (cosimplicialHomMap f.diagram).app Z ≫
            KanLiftAction.comparison hcof hfib X Z) ∧
      (∀ (Z Z' : C) (h : Z ⟶ Z'),
        prod.map (𝟙 _) ((cosimplicialHom Y.resolution.obj).map h) ≫ H Z' =
          H Z ≫ (KanLiftAction.targetFunctor hcof hfib X).map h) := by
  obtain ⟨e, he⟩ := KanLiftCoherence.chosen_comparison hcof hfib f
  exact ⟨fun Z => KanLiftCoherence.intervalAction hcof hfib X Y f.base Z e, he,
    fun Z Z' h => KanLiftCoherence.intervalAction_target_naturality hcof hfib X Y f.base h e⟩

-- The identity comparison ends at the original comparison map itself.
-- This also tests the actual Kan target and weak equivalence at a fibrant Z.
example (X : ResolutionObject C) (Z : C) [IsFibrant Z] :
    SSet.KanComplex (KanLiftAction.target hcof hfib X Z) ∧
      weakEquivalences SSet.{v} (KanLiftAction.comparison hcof hfib X Z) ∧
      ∃ H : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⨯
          (cosimplicialHom X.resolution.obj).obj Z ⟶ KanLiftAction.target hcof hfib X Z,
        prod.map (SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2))) (𝟙 _) ≫ H =
          prod.snd ≫ KanLiftCoherence.chosenMap X X (𝟙 X.base) Z ≫
            KanLiftAction.comparison hcof hfib X Z ∧
        prod.map (SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2))) (𝟙 _) ≫ H =
          prod.snd ≫ KanLiftAction.comparison hcof hfib X Z := by
  obtain ⟨e, he⟩ := KanLiftCoherence.identity hcof hfib X
  exact ⟨KanLiftAction.target_kanComplex hcof hfib X Z,
    KanLiftAction.comparison_weakEquivalence hcof hfib X Z,
    KanLiftCoherence.intervalAction hcof hfib X X (𝟙 X.base) Z e, he Z⟩

-- A composite in C has the correctly ordered precomposition at the second endpoint.
example (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y.base ⟶ W.base)
    (Z : C) :
    ∃ H : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⨯
        (cosimplicialHom W.resolution.obj).obj Z ⟶ KanLiftAction.target hcof hfib X Z,
      prod.map (SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2))) (𝟙 _) ≫ H =
        prod.snd ≫ KanLiftCoherence.chosenMap X W (f ≫ g) Z ≫
          KanLiftAction.comparison hcof hfib X Z ∧
      prod.map (SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2))) (𝟙 _) ≫ H =
        prod.snd ≫ KanLiftCoherence.chosenMap Y W g Z ≫
          KanLiftCoherence.chosenMap X Y f Z ≫ KanLiftAction.comparison hcof hfib X Z := by
  obtain ⟨e, he⟩ := KanLiftCoherence.composition hcof hfib X Y W f g
  exact ⟨KanLiftCoherence.intervalAction hcof hfib X W (f ≫ g) Z e, he Z⟩

-- Every dimension and every simplicial subcomplex: extend one lift family once,
-- then act on the entire original Hom for every Z. No product-preserving R.
example (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (n : ℕ)
    (b : (SSet.boundary.{v} n).toSSet ⟶ ResolutionLiftSpace.obj X Y f) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ ResolutionLiftSpace.obj X Y f,
      (SSet.boundary.{v} n).ι ≫ e = b ∧
      ∀ Z : C,
        prod.map (SSet.boundary.{v} n).ι (𝟙 _) ≫
            KanLiftAction.parameterized hcof hfib X Y f Z (prod.fst ≫ e) prod.snd =
          KanLiftAction.parameterized hcof hfib X Y f Z (prod.fst ≫ b) prod.snd :=
  KanLiftCoherence.boundary_extension hcof hfib X Y f _ b

end ArbitrarySource

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.KanLiftAction,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.KanLiftCoherence]
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
  unless modules.size == expected.size do throwError "Some lift coherence modules were not audited"
  logInfo m!"Kan lift coherence audit passed: {count} declarations in {modules.size} modules, \
    standard axioms only."
