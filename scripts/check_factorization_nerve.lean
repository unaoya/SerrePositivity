import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open SerrePositivity SerrePositivity.HomotopyFunctionComplex

section GeneralCategory
variable {D : Type u} [Category.{v} D] {Y V : D} (g : Y ⟶ V) {n m : ℕ}

-- No model structure, smallness, or equality of the object and Hom universes is required.
example : IsInitial (ArrowFactorization.source g) := ArrowFactorization.source_isInitial g
example : IsTerminal (ArrowFactorization.target g) := ArrowFactorization.target_isTerminal g

example : (Functor.const (ArrowFactorization g)).obj (ArrowFactorization.source g) ⟶ 𝟭 _ :=
  ArrowFactorization.fromSourceNatTrans g

example : 𝟭 (ArrowFactorization g) ⟶ (Functor.const _).obj (ArrowFactorization.target g) :=
  ArrowFactorization.toTargetNatTrans g

example (c : AnchoredChain g n) : AnchoredChain.fromDiagram (AnchoredChain.cutDiagram c) = c :=
  AnchoredChain.fromDiagram_cutDiagram c

example (F : Fin (n + 1) ⥤ ArrowFactorization g) :
    AnchoredChain.cutDiagram (AnchoredChain.fromDiagram F) = F :=
  AnchoredChain.cutDiagram_fromDiagram F

example (F : Fin (n + 1) ⥤ ArrowFactorization g) (θ : Fin (m + 1) →o Fin (n + 1)) :
    AnchoredChain.fromDiagram (θ.monotone.functor ⋙ F) =
      (AnchoredChain.fromDiagram F).reindex θ := AnchoredChain.fromDiagram_reindex F θ

-- An actual simplicial isomorphism, not merely a bijection in each degree.
example : nerve (ArrowFactorization g) ≅ AnchoredChain.simplicial g := AnchoredChain.nerveIso g

example : (AnchoredChain.nerveIso g).hom ≫ (AnchoredChain.nerveIso g).inv = 𝟙 _ :=
  (AnchoredChain.nerveIso g).hom_inv_id

example : (AnchoredChain.nerveIso g).inv ≫ (AnchoredChain.nerveIso g).hom = 𝟙 _ :=
  (AnchoredChain.nerveIso g).inv_hom_id

example {a b : SimplexCategoryᵒᵖ} (θ : a ⟶ b) :
    (nerve (ArrowFactorization g)).map θ ≫ (AnchoredChain.nerveIso g).hom.app b =
      (AnchoredChain.nerveIso g).hom.app a ≫ (AnchoredChain.simplicial g).map θ :=
  (AnchoredChain.nerveIso g).hom.naturality θ
end GeneralCategory

section ArbitraryModel
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {X Y V : ResolutionObject C} (f : X.base ⟶ Y.base) {g : Y ⟶ V} {n : ℕ}
  (F : Fin (n + 1) ⥤ ArrowFactorization g)

-- The identification retains the actual previously selected comparison triangles.
example (k : Fin (n + 1)) :
    AnchoredPostComparison.triangle hcof hfib f (AnchoredChain.fromDiagram F) k =
      AnchoredPostComparison.factorTriangle hcof hfib f (F.obj k) :=
  AnchoredPostComparison.fromDiagram_triangle hcof hfib f F k

example {i j : Fin (n + 1)} (h : i ⟶ j) :
    (AnchoredChain.fromDiagram F).diagram.map h = (F.map h).hom := rfl
end ArbitraryModel

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.CategoryTheory.ArrowFactorizationCategory,
    `SerrePositivity.CategoryTheory.AnchoredChainNerve,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AnchoredPostComparison]
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
    throwError "Some factorization nerve modules were not audited"
  logInfo m!"Factorization nerve audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
