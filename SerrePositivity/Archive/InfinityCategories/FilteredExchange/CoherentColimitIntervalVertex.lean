module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitLowerTriangle
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.HomotopyVertexPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantDiagramTransformation

/-!
概要：余極限関手の指定辺を、元の両余錐の頂点間の全区間族として読む。
方針：端点の等式だけを反映し、定値図式の第二辺との全円柱を照合する。
規約：指定一次単体を変更しない。使われ方：下三角形の普遍 pointed-space 輸送比較。
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

/-- 元の余極限の指定辺を、元の両 native 余錐の頂点の区間写像空間で読む。 -/
def coherentColimitIntervalVertex : (intervalMappingSpace
    (coherentDiagramTotalCocone F).vertex (coherentDiagramTotalVertex G)) _⦋0⦌ :=
  intervalMappingVertexOfEdge ⟨(coherentColimitFunctorEdge B H).edge,
    (coherentColimitFunctorEdge B H).src_eq.trans (coherentDiagramTotalCocone_vertex F).symm,
    (coherentColimitFunctorEdge B H).tgt_eq⟩

/-- 区間族の全円柱は、一点パラメータを補った元の指定辺そのもの。 -/
lemma coherentColimitIntervalVertex_uncurry :
    intervalMappingUncurry (SSet.yonedaEquiv.symm (coherentColimitIntervalVertex B H)) =
      fst (Δ[1] : SSet.{u + 1}) Δ[0] ≫
        SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B H).edge :=
  intervalMappingUncurry_vertex _

/-- 元の指定区間族の定値図式への作用は、下三角形の元の第二辺の全族そのもの。 -/
lemma coherentColimitIntervalVertex_constant :
    constantDiagramTransformation ((SSet.uliftFunctor.{u + 1, u}).obj B)
      (SSet.yonedaEquiv.symm (coherentColimitIntervalVertex B H)) =
      SSet.yonedaEquiv.symm (coherentVertexOfHomotopy
        (coherentColimitIntervalConstantHomotopy B H)) := by
  apply constantTransformationPrism_injective
  rw [constantDiagramTransformation_prism, coherentColimitIntervalVertex_uncurry]
  refine Eq.trans ?_ (constantTransformationPrism_coherentVertex
    (coherentColimitIntervalConstantHomotopy B H)).symm
  have he := (congrArg uncurry (coherentColimitConstantEdge_curry B H)).trans
    (uncurry_curry _)
  exact (congrArg (fun q =>
    fst (((SSet.uliftFunctor.{u + 1, u}).obj B) ⊗ Δ[1]) Δ[0] ≫ q) he).symm

end SerrePositivity.InfinityCategories.F2
