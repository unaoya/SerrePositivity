module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitIntervalVertex

/-!
概要：元の余錐の両頂点を保持したまま、元の余極限辺の全区間族を取り出す。
方針：同じ一次単体の両端だけを元の余錐の頂点へ表示変更する。
規約：native 頂点への表示変更を先送りする。使われ方：元の定値三角形の三辺を照合する。
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

/-- 元の指定辺を元の両余錐頂点の間の区間写像空間で読む。 -/
def coherentColimitRawIntervalVertex : (intervalMappingSpace
    (coherentDiagramTotalCocone F).vertex (coherentDiagramTotalCocone G).vertex) _⦋0⦌ :=
  intervalMappingVertexOfEdge ⟨(coherentColimitFunctorEdge B H).edge,
    (coherentColimitFunctorEdge B H).src_eq.trans (coherentDiagramTotalCocone_vertex F).symm,
    (coherentColimitFunctorEdge B H).tgt_eq.trans (coherentDiagramTotalCocone_vertex G).symm⟩

/-- 全区間の円柱は、元の指定余極限辺に一点係数を添えたものそのもの。 -/
lemma coherentColimitRawIntervalVertex_uncurry :
    intervalMappingUncurry (SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B H)) =
      fst (Δ[1] : SSet.{u + 1}) Δ[0] ≫
        SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B H).edge :=
  intervalMappingUncurry_vertex _

/-- 元の区間の定値図式の作用は、元の定値余極限辺の同じ全変換族。 -/
lemma coherentColimitRawIntervalVertex_constant :
    constantDiagramTransformation ((SSet.uliftFunctor.{u + 1, u}).obj B)
      (SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B H)) =
      SSet.yonedaEquiv.symm (coherentVertexOfHomotopy
        (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B H))) := by
  apply constantTransformationPrism_injective
  rw [constantDiagramTransformation_prism, coherentColimitRawIntervalVertex_uncurry]
  refine Eq.trans ?_ (constantTransformationPrism_coherentVertex
    (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B H))).symm
  have he := (congrArg uncurry (coherentColimitConstantEdge_curry B H)).trans (uncurry_curry _)
  exact (congrArg (fun q =>
    fst (((SSet.uliftFunctor.{u + 1, u}).obj B) ⊗ Δ[1]) Δ[0] ≫ q) he).symm

end SerrePositivity.InfinityCategories.F2
