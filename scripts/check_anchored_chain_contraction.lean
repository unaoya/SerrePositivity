import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity

section NaturalTransformation
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {F G : C ⥤ D} (α : F ⟶ G)

-- Independent object and Hom universes, with no model structure or fibrancy hypothesis.
example : SSet.Homotopy (nerveMap F) (nerveMap G) := NerveHomotopy.homotopy α

example : SSet.ι₀ ≫ NerveHomotopy.hom α = nerveMap F := NerveHomotopy.at_zero α
example : SSet.ι₁ ≫ NerveHomotopy.hom α = nerveMap G := NerveHomotopy.at_one α

-- It is one actual simplicial map and so commutes with all ordinal operators.
example {a b : SimplexCategoryᵒᵖ} (θ : a ⟶ b) :
    (nerve C ⊗ SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)).map θ ≫
        (NerveHomotopy.hom α).app b =
      (NerveHomotopy.hom α).app a ≫ (nerve D).map θ :=
  (NerveHomotopy.hom α).naturality θ
end NaturalTransformation

section ArbitraryCategory
variable {D : Type u} [Category.{v} D] {Y V : D} (g : Y ⟶ V)

example : AnchoredChain.basePoint g ≫ AnchoredChain.collapse g = 𝟙 _ :=
  AnchoredChain.basePoint_collapse g

-- This contracts the actual simplicial set already identified with the factorization nerve.
example : SSet.Homotopy (AnchoredChain.collapse g ≫ AnchoredChain.basePoint g)
    (𝟙 (AnchoredChain.simplicial g)) := AnchoredChain.contraction g

example : SSet.ι₀ ≫ (AnchoredChain.contraction g).h =
    AnchoredChain.collapse g ≫ AnchoredChain.basePoint g := (AnchoredChain.contraction g).h₀

example : SSet.ι₁ ≫ (AnchoredChain.contraction g).h = 𝟙 (AnchoredChain.simplicial g) :=
  (AnchoredChain.contraction g).h₁
end ArbitraryCategory

section ArbitraryModel
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  {X Y : HomotopyFunctionComplex.ResolutionObject C} (g : X ⟶ Y)

-- Strict resolution arrows use the same construction, without chosen functorial factorizations.
example : SSet.Homotopy (AnchoredChain.collapse g ≫ AnchoredChain.basePoint g)
    (𝟙 (AnchoredChain.simplicial g)) := AnchoredChain.contraction g
end ArbitraryModel

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.CategoryTheory.NerveHomotopy,
    `SerrePositivity.CategoryTheory.AnchoredChainContraction]
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
    throwError "Some chain contraction modules were not audited"
  logInfo m!"Anchored chain contraction audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
