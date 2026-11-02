module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawSpaceEdgeValue

/-!
概要：元の三余錐の頂点を、元の余極限二単体の同じ三つの Kan 対象の標準頂点へ揃える。
方針：実三辺の面式と元の Space 辺の両端の回収式を使う。
規約：頂点等式は実辺から回収する。使われ方：三辺の指定値比較の合成と指定 path の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)

/-- 元の最初の余錐頂点は、同じ余極限二単体の最初の対象の標準頂点。 -/
lemma coherentColimitApex_raw_zero_vertex :
    (coherentDiagramTotalCocone F).vertex =
      spaceInfinityVertex ((coherentColimitApexTriangle B T).obj ⟨ULift.up 0⟩) :=
  (spaceEdge_source_to_object (coherentColimitRawSpaceEdge B a)).trans
    (congrArg (fun e : SpaceInfinity.{u} _⦋1⦌ => spaceInfinityVertex (e.obj ⟨ULift.up 0⟩))
      (coherentColimitRawSpaceEdge_first B a T))

/-- 元の中間余錐頂点も、同じ余極限二単体の中間対象の標準頂点。 -/
lemma coherentColimitApex_raw_one_vertex :
    (coherentDiagramTotalCocone G).vertex =
      spaceInfinityVertex ((coherentColimitApexTriangle B T).obj ⟨ULift.up 1⟩) :=
  (spaceEdge_target_to_object (coherentColimitRawSpaceEdge B a)).trans
    (congrArg (fun e : SpaceInfinity.{u} _⦋1⦌ => spaceInfinityVertex (e.obj ⟨ULift.up 1⟩))
      (coherentColimitRawSpaceEdge_first B a T))

/-- 元の最後の余錐頂点も、同じ余極限二単体の最後の対象の標準頂点。 -/
lemma coherentColimitApex_raw_two_vertex :
    (coherentDiagramTotalCocone J).vertex =
      spaceInfinityVertex ((coherentColimitApexTriangle B T).obj ⟨ULift.up 2⟩) :=
  (spaceEdge_target_to_object (coherentColimitRawSpaceEdge B b)).trans
    (congrArg (fun e : SpaceInfinity.{u} _⦋1⦌ => spaceInfinityVertex (e.obj ⟨ULift.up 1⟩))
      (coherentColimitRawSpaceEdge_last B a T))

end SerrePositivity.InfinityCategories.F2
