import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open CoherentLiftRelative

section StrictParameters
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {I J K : Type v} (α : I → J) (β : J → K)

example : TriangleBook.reindex α ≫ TriangleBook.reindex β = TriangleBook.reindex (β ∘ α) :=
  TriangleBook.reindex_comp α β

example : KanTriangleFamily.reindex hcof hfib α ≫ KanTriangleFamily.reindex hcof hfib β =
    KanTriangleFamily.reindex hcof hfib (β ∘ α) := KanTriangleFamily.reindex_comp _ _ α β

example : KanTriangleFamily.reindex hcof hfib (id : I → I) = 𝟙 _ :=
  KanTriangleFamily.reindex_id _ _ I
end StrictParameters

section ArbitrarySource
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {n : ℕ} (F : Fin (n + 1) ⥤ ResolutionObject C)
  (X : ResolutionObject C) (f : X.base ⟶ (F.obj 0).base)
  {I J : Type v} (cuts : I → Fin (n + 1)) (α : J → I)

-- The previous full-chain construction is recovered literally.
example : PostChainReindexing.comparison hcof hfib F X f
    (fun i : ULift.{v} (Fin (n + 1)) => i.down) =
      PostChainKanParameter.comparison hcof hfib F X f :=
  PostChainReindexing.full_comparison hcof hfib F X f

-- No injectivity or order assumption: indices may be selected, reordered, or repeated.
example (j : J) :
    (TriangleBook.triangle J j ≫ KanTriangleFamily.inclusion hcof hfib J) ≫
      PostChainReindexing.comparison hcof hfib F X f (cuts ∘ α) =
        PostCompositionChain.cutTriangle hcof hfib F X f (cuts (α j)) :=
  PostChainReindexing.comparison_cut hcof hfib F X f (cuts ∘ α) j

local notation "H" => PostChainReindexing.reindexHomotopy hcof hfib F X f cuts α
local notation "d" => postEdge hcof hfib X (F.obj 0) (F.obj (Fin.last n)) f
  (PostCompositionChain.total F)
local notation "b" => TriangleBook.desc d
  (fun j : J => PostCompositionChain.cutTriangle hcof hfib F X f (cuts (α j)))
  (fun j => PostCompositionChain.cutTriangle_direct hcof hfib F X f (cuts (α j)))

example : (KanTriangleFamily.parameter hcof hfib J) ◁
    SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ (H).hom =
      (KanTriangleFamily.parameter hcof hfib J) ◁ RelativeChoiceSpace.pointUnitIso.hom ≫
        (ρ_ _).hom ≫ PostChainReindexing.comparison hcof hfib F X f (cuts ∘ α) := (H).at_zero

example : (KanTriangleFamily.parameter hcof hfib J) ◁
    SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ (H).hom =
      (KanTriangleFamily.parameter hcof hfib J) ◁ RelativeChoiceSpace.pointUnitIso.hom ≫
        (ρ_ _).hom ≫ (KanTriangleFamily.reindex hcof hfib α ≫
          PostChainReindexing.comparison hcof hfib F X f cuts) := (H).at_one

-- The entire selected triangle family stays fixed along the homotopy.
example : KanTriangleFamily.inclusion hcof hfib J ▷
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ≫ (H).hom =
      TriangleBook.obj J ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫ b := (H).relative

-- Evaluating that same homotopy also fixes all original strict-lift vertices.
example : vertexInclusion X (F.obj 0) f ▷
    (KanTriangleFamily.parameter hcof hfib J ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1)) ≫
      RelativeChoiceSpace.family (vertexInclusion X (F.obj 0) f)
        (postBoundary X (F.obj 0) (F.obj (Fin.last n)) f (PostCompositionChain.total F)) (H).hom =
      vertices X (F.obj 0) f ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫
          postBoundary X (F.obj 0) (F.obj (Fin.last n)) f (PostCompositionChain.total F) :=
  RelativeChoiceSpace.family_fixed_boundary _ _ _
end ArbitrarySource

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.TriangleBookMaps,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanTriangleFamily,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PostChainReindexing]
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
  unless modules.size == expected.size do throwError "Some reindexing modules were not audited"
  logInfo m!"Post-chain reindexing audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
