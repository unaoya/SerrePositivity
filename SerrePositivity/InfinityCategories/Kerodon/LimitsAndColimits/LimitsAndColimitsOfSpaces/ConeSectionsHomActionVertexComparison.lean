module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.PointedIntervalTransportVertexComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalVertices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.FixedApexConeEdgeComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeSectionsNativeComparison

/-!
概要：元の錐の全切断への全 Hom 作用は、指定された錐の辺の標準後合成と可換。
方針：元の native Hom 比較の辺の同型を、同じ全切断作用の比較で移す。
規約：全 Hom をパラメータにし、試験空間の点へ弱めない。
使われ方：G8 の切断錐から指定極限への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions MorphismSpaces Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

attribute [local instance] IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 概要：同じ区間頂点への同型の下で Hom 作用を元の辺輸送と比較する。
方針：pointed 輸送の全族比較を同じ頂点で評価し、同じ切断写像を後合成する。
規約：始点 fiber の全体をパラメータとして保つ。
使われ方：G8 の指定極限錐の値の写像への接続。 -/
def coneSectionsHomAction_intervalVertexIso {B : SSet.{u + 1}}
    {F : B ⟶ SpaceInfinity.{u}} (c : JoinCone F) (z : SpaceInfinity.{u} _⦋0⦌)
    (s : (Basic.pinchedHom z c.vertex) _⦋0⦌) (e : SpaceInfinity.{u}.Edge z c.vertex)
    (hs : VertexIso ((pinchedHomToIntervalMappingSpace z c.vertex).app _ s)
      (intervalMappingVertexOfEdge e)) :
    FunctorIso
      ((functorVertexEquiv _ _).symm ((coneSectionsHomAction c z).app _ s))
      (edgeTransport pointedSpaceProjection e ≫
        coneSectionsMap c) := by
  let j := pinchedHomToIntervalMappingSpace z c.vertex
  let h := pointedIntervalTransport_vertex_edgeIso j s e hs
  have he : (functorVertexEquiv _ _).symm ((coneSectionsHomAction c z).app _ s) =
      (functorVertexEquiv _ _).symm ((pointedIntervalTransport j).map.app _ s) ≫
        coneSectionsMap c := by
    apply functorVertex_injective
    have hcv : functorVertex ((functorVertexEquiv _ _).symm
        ((coneSectionsHomAction c z).app _ s)) = (coneSectionsHomAction c z).app _ s :=
      (functorVertexEquiv _ _).apply_symm_apply _
    rw [hcv]
    let k := (functorVertexEquiv _ _).symm ((pointedIntervalTransport j).map.app _ s)
    have hk : functorVertex k = (pointedIntervalTransport j).map.app _ s :=
      (functorVertexEquiv _ _).apply_symm_apply _
    change ((ihom _).map (coneSectionsMap c)).app _
      ((pointedIntervalTransport j).map.app _ s) = functorVertex (k ≫ coneSectionsMap c)
    rw [← hk]
    unfold functorVertex
    rw [← curry'_ihom_map]
    rfl
  rw [he]
  exact h.postcomp (coneSectionsMap c)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
