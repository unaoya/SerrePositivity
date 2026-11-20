import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

noncomputable section
universe v u vH uH
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.Reedy
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
  (cosimplicialHom)

variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (A : SimplexCategory ⥤ C)
  (hA : reedyLeft simplex (cofibrations C) (initial.to A))
  (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))

-- The source is an arbitrary model category, without tensor, enrichment,
-- local presentability or chosen functorial factorization assumptions.
example : SerrePositivity.Quillen.IsRightQuillen (cosimplicialHom A) :=
  cosimplicialHom_isRightQuillen hcof hfib A hA hconst

example {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
    [L.IsLocalization (weakEquivalences SSet.{v})] :
    (cosimplicialHom A ⋙ L).HasPointwiseRightDerivedFunctor (weakEquivalences C) :=
  cosimplicialHom_hasPointwiseRightDerived hcof hfib A hA hconst L

-- Fixed mono/Kan classes suffice; no concrete model existence is imported.
example : SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{v}
    SSet.modelCategoryQuillen.I.{v} SSet.modelCategoryQuillen.J.{v} :=
  SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib

example : SerrePositivity.Quillen.IsQuillenBifunctor
    (CategoryTheory.MonoidalCategory.curriedTensor SSet.{v}) :=
  SerrePositivity.SimplicialModel.simplicial_isQuillenBifunctor hcof hfib

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.Generators,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.ModelCompatibility,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameRightQuillen]
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
  logInfo m!"Frame right Quillen and shared simplicial model audit passed: {count} declarations in {seen.size} modules."
