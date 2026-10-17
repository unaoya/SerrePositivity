import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open CoherentLiftRelative

section ArbitraryChain
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {n : ℕ} (F : Fin (n + 1) ⥤ ResolutionObject C)
  (X : ResolutionObject C) (f : X.base ⟶ (F.obj 0).base)

-- An arbitrary finite chain, with no object/Hom universe equality or source factorization data.
example (i : Fin (n + 1)) :
    PostCompositionChain.prefixMap F i ≫ PostCompositionChain.suffixMap F i =
      PostCompositionChain.total F := PostCompositionChain.prefix_suffix F i

-- The cut triangles are exactly the previously selected prefix/suffix comparison triangles.
example (i : Fin (n + 1)) : PostCompositionChain.cutTriangle hcof hfib F X f i =
    CoherentLiftPostComposition.triangle hcof hfib X (F.obj 0) (F.obj i) (F.obj (Fin.last n))
      f (PostCompositionChain.prefixMap F i) (PostCompositionChain.suffixMap F i) ≫
        PostCompositionChain.choiceCast f (PostCompositionChain.prefix_suffix F i) := rfl

-- All three previously selected edges of every cut triangle are retained.
example (i : Fin (n + 1)) (k : Fin 3) :
    SSet.stdSimplex.δ k ≫ PostCompositionChain.cutTriangle hcof hfib F X f i =
      CoherentLiftPostComposition.faces hcof hfib X (F.obj 0) (F.obj i) (F.obj (Fin.last n))
        f (PostCompositionChain.prefixMap F i) (PostCompositionChain.suffixMap F i) k ≫
          PostCompositionChain.choiceCast f (PostCompositionChain.prefix_suffix F i) :=
  PostCompositionChain.cutTriangle_face hcof hfib F X f i k

-- All cuts have the same actual direct edge, not merely homotopic direct edges.
example (i j : Fin (n + 1)) :
    SSet.stdSimplex.δ (1 : Fin 3) ≫ PostCompositionChain.cutTriangle hcof hfib F X f i =
      SSet.stdSimplex.δ (1 : Fin 3) ≫ PostCompositionChain.cutTriangle hcof hfib F X f j :=
  (PostCompositionChain.cutTriangle_direct hcof hfib F X f i).trans
    (PostCompositionChain.cutTriangle_direct hcof hfib F X f j).symm

example : SSet.KanComplex (PostChainKanParameter.parameter hcof hfib F) :=
  PostChainKanParameter.parameter_kanComplex hcof hfib F

-- The global Kan parameter retains every entire selected cut triangle.
example (i : Fin (n + 1)) : PostChainKanParameter.cut hcof hfib F i ≫
    PostChainKanParameter.comparison hcof hfib F X f =
      PostCompositionChain.cutTriangle hcof hfib F X f i :=
  PostChainKanParameter.comparison_cut hcof hfib F X f i

example :
    (TriangleBook.sharedEdge (ULift.{v} (Fin (n + 1))) ≫
      PostChainKanParameter.inclusion hcof hfib F) ≫
        PostChainKanParameter.comparison hcof hfib F X f =
          postEdge hcof hfib X (F.obj 0) (F.obj (Fin.last n)) f (PostCompositionChain.total F) :=
  PostChainKanParameter.comparison_direct hcof hfib F X f

example : vertexInclusion X (F.obj 0) f ▷ PostChainKanParameter.parameter hcof hfib F ≫
    RelativeChoiceSpace.family (vertexInclusion X (F.obj 0) f)
      (postBoundary X (F.obj 0) (F.obj (Fin.last n)) f (PostCompositionChain.total F))
      (PostChainKanParameter.comparison hcof hfib F X f) =
    vertices X (F.obj 0) f ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
      RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫
        postBoundary X (F.obj 0) (F.obj (Fin.last n)) f (PostCompositionChain.total F) :=
  PostChainKanParameter.fixed_boundary hcof hfib F X f

-- Same global choice, every Z and parameter, without fibrancy of Z.
example (i : Fin (n + 1)) (Z : C)
    (t : CoherentLiftTuples.obj X (F.obj 0) f ⊗ PostChainKanParameter.parameter hcof hfib F ⟶
      (cosimplicialHom (F.obj (Fin.last n)).resolution.obj).obj Z) :
    CoherentLiftTuples.obj X (F.obj 0) f ◁ PostChainKanParameter.cut hcof hfib F i ≫
      KanLiftAction.parameterized hcof hfib X (F.obj (Fin.last n))
        (f ≫ (PostCompositionChain.total F).base) Z
        (RelativeChoiceSpace.family (vertexInclusion X (F.obj 0) f)
          (postBoundary X (F.obj 0) (F.obj (Fin.last n)) f (PostCompositionChain.total F))
          (PostChainKanParameter.comparison hcof hfib F X f)) t =
      KanLiftAction.parameterized hcof hfib X (F.obj (Fin.last n))
        (f ≫ (PostCompositionChain.total F).base) Z
        (RelativeChoiceSpace.family (vertexInclusion X (F.obj 0) f)
          (postBoundary X (F.obj 0) (F.obj (Fin.last n)) f (PostCompositionChain.total F))
          (PostCompositionChain.cutTriangle hcof hfib F X f i))
        ((CoherentLiftTuples.obj X (F.obj 0) f ◁ PostChainKanParameter.cut hcof hfib F i) ≫ t) :=
  PostChainKanParameter.action_cut hcof hfib F X f i Z t

-- Zero-arrow chains, including the identity factorization, are covered by the same construction.
example (Y : ResolutionObject C) : SSet.KanComplex
    (PostChainKanParameter.parameter hcof hfib ((Functor.const (Fin 1)).obj Y)) :=
  PostChainKanParameter.parameter_kanComplex hcof hfib ((Functor.const (Fin 1)).obj Y)
end ArbitraryChain

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.TriangleBook,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanReplacement,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.PostCompositionChain,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.PostChainKanParameter]
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
    throwError "Some postcomposition chain modules were not audited"
  logInfo m!"Postcomposition chain audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
