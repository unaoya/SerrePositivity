import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

-- The value-side factorization and functor are constructed, not supplied.
example [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp) (K : SSet.{v}) :
    SSet.KanComplex ((SerrePositivity.SimplicialModel.KanReplacement.functor hcof hfib).obj K) ∧
      weakEquivalences SSet.{v} ((SerrePositivity.SimplicialModel.KanReplacement.unit hcof hfib).app K) :=
  ⟨SerrePositivity.SimplicialModel.KanReplacement.kanComplex hcof hfib K,
    SerrePositivity.SimplicialModel.KanReplacement.unit_weakEquivalence hcof hfib K⟩

-- Arbitrary model source: no specified functorial factorization, enrichment,
-- local presentability or diagonal source cofibrancy.
example {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    (X : ResolutionObject C) (Z : C) [IsFibrant Z] :
    SSet.KanComplex (KanLiftAction.target hcof hfib X Z) ∧
      weakEquivalences SSet.{v} (KanLiftAction.comparison hcof hfib X Z) :=
  ⟨KanLiftAction.target_kanComplex hcof hfib X Z,
    KanLiftAction.comparison_weakEquivalence hcof hfib X Z⟩

example {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
    [Q.IsLocalization (weakEquivalences C)] (X : ResolutionObject C) (Z : C) [IsFibrant Z] :
    SSet.π₀ (KanLiftAction.target hcof hfib X Z) ≃ (Q.obj X.base ⟶ Q.obj Z) :=
  KanLiftAction.piZeroLocalizationEquiv hcof hfib Q X Z

-- The replaced target is functorial in Z and retains weak invariance.
example {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    (X : ResolutionObject C) {Z Z' : C} [IsFibrant Z] [IsFibrant Z']
    (f : Z ⟶ Z') (hf : weakEquivalences C f) :
    weakEquivalences SSet.{v} ((KanLiftAction.targetFunctor hcof hfib X).map f) :=
  KanLiftAction.target_map_weakEquivalence hcof hfib X f hf

-- All higher boundary actions extend without a product-preservation assumption on replacement.
example {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (Z : C) (n : ℕ)
    (b : (SSet.boundary.{v} n).toSSet ⟶ ResolutionLiftSpace.obj X Y f)
    (t : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶
      (cosimplicialHom Y.resolution.obj).obj Z) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ ResolutionLiftSpace.obj X Y f,
      (SSet.boundary n).ι ≫ e = b ∧
      (SSet.boundary n).ι ≫ KanLiftAction.parameterized hcof hfib X Y f Z e t =
        KanLiftAction.parameterized hcof hfib X Y f Z b ((SSet.boundary n).ι ≫ t) :=
  KanLiftAction.extends_action hcof hfib X Y f Z _ b t

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanReplacement,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.KanLiftAction]
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
  unless modules.size == expected.size do throwError "Some Kan lift action modules were not audited"
  logInfo m!"Kan lift action audit passed: {count} declarations in {modules.size} modules, standard axioms only."
