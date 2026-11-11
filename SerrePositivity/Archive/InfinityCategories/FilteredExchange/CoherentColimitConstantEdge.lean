module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentColimitUnitSquare
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseFunctorFiber

/-!
概要：余極限関手の元の指定辺を、元の余錐の頂点の定値図式間の辺へ移す。
方針：定値図式関手で写し、元の余錐の頂点式で端点だけを合わせる。
規約：一次単体を変更しない。使われ方：単位の自然性の合成整合式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 余極限の元の指定辺を、元の両余錐の頂点の定値図式間で読む。 -/
def coherentColimitConstantEdge : SSet.Truncated.Edge
    (X := (truncation 2).obj
      ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}))
    (functorVertex (SSet.const (coherentDiagramTotalCocone F).vertex))
    (functorVertex (SSet.const (coherentDiagramTotalCocone G).vertex)) := by
  let e := (coherentColimitFunctorEdge B H).map ((truncation 2).map
    (constantDiagram ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u}))
  refine ⟨e.edge, e.src_eq.trans ?_, e.tgt_eq.trans ?_⟩
  · change (constantDiagram ((SSet.uliftFunctor.{u + 1, u}).obj B)
      SpaceInfinity.{u}).app (Opposite.op ⦋0⦌) (coherentDiagramTotalVertex F) = _
    rw [constantDiagram_vertex, coherentDiagramTotalCocone_vertex]
  · change (constantDiagram ((SSet.uliftFunctor.{u + 1, u}).obj B)
      SpaceInfinity.{u}).app (Opposite.op ⦋0⦌) (coherentDiagramTotalVertex G) = _
    rw [constantDiagram_vertex, coherentDiagramTotalCocone_vertex]

/-- 定値図式の指定辺は、元の余極限の指定辺から底の変数を忘れた円柱を curry したもの。 -/
lemma coherentColimitConstantEdge_curry :
    SSet.yonedaEquiv.symm (coherentColimitConstantEdge B H).edge =
      curry (snd ((SSet.uliftFunctor.{u + 1, u}).obj B) Δ[1] ≫
        SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B H).edge) := by
  change SSet.yonedaEquiv.symm ((constantDiagram
    ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u}).app (Opposite.op ⦋1⦌)
    (coherentColimitFunctorEdge B H).edge) = _
  rw [← SSet.yonedaEquiv_symm_comp]
  apply uncurry_injective
  rw [uncurry_comp_constantDiagram, uncurry_curry]

end SerrePositivity.InfinityCategories.F2
