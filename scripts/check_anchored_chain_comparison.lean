import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open CoherentLiftRelative

section GeneralCategory
variable {D : Type u} [Category.{v} D] {Y V : D} {g : Y ⟶ V} {n m l : ℕ}
  (c : AnchoredChain g n) (θ : Fin (m + 1) →o Fin (n + 1))
  (φ : Fin (l + 1) →o Fin (m + 1))

example (k : Fin (m + 1)) : (c.reindex θ).cut k = c.cut (θ k) := c.cut_reindex θ k

example : c.reindex (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) = c := c.reindex_id

example : (c.reindex θ).reindex φ = c.reindex (θ.comp φ) := c.reindex_comp θ φ

example : SSet.{max u v} := AnchoredChain.simplicial g

example (k : Fin (l + 1)) : ((c.reindex θ).reindex φ).cut k = (c.reindex (θ.comp φ)).cut k :=
  c.cut_reindex_comp θ φ k

-- This includes outer faces: no preservation of the first or last internal vertex is assumed.
example (c' : AnchoredChain g (n + 1)) (j : Fin (n + 2)) (k : Fin (n + 1)) :
    (c'.reindex (SimplexCategory.δ j).toOrderHom).cut k =
      c'.cut ((SimplexCategory.δ j).toOrderHom k) := c'.cut_reindex _ k

-- Degeneracy maps repeat vertices and are covered by the same actual factorization equality.
example (j : Fin (n + 1)) (k : Fin (n + 2)) :
    (c.reindex (SimplexCategory.σ j).toOrderHom).cut k =
      c.cut ((SimplexCategory.σ j).toOrderHom k) := c.cut_reindex _ k
end GeneralCategory

section ArbitraryModel
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {X Y V : ResolutionObject C} (f : X.base ⟶ Y.base) {g : Y ⟶ V}
  {n m : ℕ} (c : AnchoredChain g n) (θ : Fin (m + 1) →o Fin (n + 1))

example (k : Fin (m + 1)) : AnchoredPostComparison.triangle hcof hfib f (c.reindex θ) k =
    AnchoredPostComparison.triangle hcof hfib f c (θ k) :=
  AnchoredPostComparison.triangle_reindex hcof hfib f c θ k

-- The diagram of the chain changes, while the external source, target, and total arrow stay fixed.
example : AnchoredPostComparison.ordinalMap c θ ≫ AnchoredPostComparison.comparison hcof hfib f c =
    AnchoredPostComparison.comparison hcof hfib f (c.reindex θ) :=
  AnchoredPostComparison.comparison_reindex hcof hfib f c θ

example (F : Fin (n + 1) ⥤ ResolutionObject C) (X : ResolutionObject C)
    (f : X.base ⟶ (F.obj 0).base) (k : Fin (n + 1)) :
    AnchoredPostComparison.triangle hcof hfib f (AnchoredChain.ofDiagram F) k =
      PostCompositionChain.cutTriangle hcof hfib F X f k :=
  AnchoredPostComparison.ofDiagram_triangle hcof hfib F X f k

local notation "H" => AnchoredPostComparison.reindexHomotopy hcof hfib f c θ
local notation "K" => KanTriangleFamily.parameter hcof hfib (ULift (Fin (m + 1)))

example : K ◁ SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ (H).hom =
    K ◁ RelativeChoiceSpace.pointUnitIso.hom ≫ (ρ_ _).hom ≫
      AnchoredPostComparison.kanComparison hcof hfib f (c.reindex θ) :=
  AnchoredPostComparison.reindexHomotopy_at_zero hcof hfib f c θ

example : K ◁ SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ (H).hom =
    K ◁ RelativeChoiceSpace.pointUnitIso.hom ≫ (ρ_ _).hom ≫
      (KanTriangleFamily.reindex hcof hfib
        (fun k : ULift.{v} (Fin (m + 1)) => (⟨θ k.down⟩ : ULift.{v} (Fin (n + 1)))) ≫
          AnchoredPostComparison.kanComparison hcof hfib f c) :=
  AnchoredPostComparison.reindexHomotopy_at_one hcof hfib f c θ

example : KanTriangleFamily.inclusion hcof hfib (ULift.{v} (Fin (m + 1))) ▷
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ≫ (H).hom =
      TriangleBook.obj (ULift.{v} (Fin (m + 1))) ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫
          AnchoredPostComparison.comparison hcof hfib f (c.reindex θ) :=
  AnchoredPostComparison.reindexHomotopy_relative hcof hfib f c θ
end ArbitraryModel

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.CategoryTheory.AnchoredChain,
    `SerrePositivity.CategoryTheory.AnchoredChainSimplicial,
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
  unless modules.size == expected.size do throwError "Some anchored chain modules were not audited"
  logInfo m!"Anchored chain comparison audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
