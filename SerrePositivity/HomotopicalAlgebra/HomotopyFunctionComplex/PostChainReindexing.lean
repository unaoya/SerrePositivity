module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PostChainKanParameter
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTriangleFamily

/-! # Selecting and repeating cut comparisons of a fixed finite chain

Arbitrary small index maps select or repeat the actual existing cut
triangles. The original full-cut extension is recovered definitionally.
Reindexing comparisons fix the whole selected triangle family.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative

namespace SerrePositivity.HomotopyFunctionComplex.PostChainReindexing
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {n : ℕ} (F : Fin (n + 1) ⥤ ResolutionObject C)
  (X : ResolutionObject C) (f : X.base ⟶ (F.obj 0).base)
  {I : Type v} (cuts : I → Fin (n + 1))

abbrev comparison := KanTriangleFamily.extension hcof hfib (vertexInclusion X (F.obj 0) f)
  (postBoundary X (F.obj 0) (F.obj (Fin.last n)) f (PostCompositionChain.total F))
  (ResolutionLiftSpace.projection X (F.obj (Fin.last n)) (f ≫ (PostCompositionChain.total F).base))
  (ResolutionLiftSpace.projection_trivialFibration hcof X (F.obj (Fin.last n))
    (f ≫ (PostCompositionChain.total F).base))
  (postEdge hcof hfib X (F.obj 0) (F.obj (Fin.last n)) f (PostCompositionChain.total F))
  (fun i => PostCompositionChain.cutTriangle hcof hfib F X f (cuts i))
  (fun i => PostCompositionChain.cutTriangle_direct hcof hfib F X f (cuts i))

lemma full_comparison : comparison hcof hfib F X f (fun i : ULift.{v} (Fin (n + 1)) => i.down) =
    PostChainKanParameter.comparison hcof hfib F X f := rfl

@[reassoc]
lemma comparison_cut (i : I) :
    (TriangleBook.triangle I i ≫ KanTriangleFamily.inclusion hcof hfib I) ≫
      comparison hcof hfib F X f cuts = PostCompositionChain.cutTriangle hcof hfib F X f (cuts i) :=
  KanTriangleFamily.extension_triangle _ _ _ _ _ _ _ _ _ i

abbrev reindexHomotopy {J : Type v} (α : J → I) :=
  KanTriangleFamily.reindexHomotopy hcof hfib (vertexInclusion X (F.obj 0) f)
    (postBoundary X (F.obj 0) (F.obj (Fin.last n)) f (PostCompositionChain.total F))
    (ResolutionLiftSpace.projection X (F.obj (Fin.last n))
      (f ≫ (PostCompositionChain.total F).base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X (F.obj (Fin.last n))
      (f ≫ (PostCompositionChain.total F).base))
    (postEdge hcof hfib X (F.obj 0) (F.obj (Fin.last n)) f (PostCompositionChain.total F))
    (fun i => PostCompositionChain.cutTriangle hcof hfib F X f (cuts i))
    (fun i => PostCompositionChain.cutTriangle_direct hcof hfib F X f (cuts i)) α

end SerrePositivity.HomotopyFunctionComplex.PostChainReindexing
