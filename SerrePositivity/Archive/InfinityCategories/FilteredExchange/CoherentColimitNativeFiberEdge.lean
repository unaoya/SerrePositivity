module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitEdgeValueComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SpaceEdgeTransportValue

/-!
概要：a6 の選択済み native 輸送を、同じ native 区間辺の実際の辺輸送に比較する。
方針：同じ普遍輸送射の二表示を評価し、元の辺での普遍輸送の比較を続ける。
規約：native 表示と辺を保持。使われ方：native 区間の Kan 値と元の値の射の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- a6 の指定 native 輸送は、同じ native 区間表示から回収した辺の輸送に同型。 -/
def coherentColimitNativeFiberEdgeIso : FunctorIso
    (coherentTotalMapNativeFiberTransport F G
      (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H)))
    (edgeTransport pointedSpaceProjection
      (intervalMappingEdgeOfVertex (coherentColimitNativeIntervalVertex B H))) := by
  let x := (coherentDiagramTotalCocone F).vertex
  let y := coherentDiagramTotalVertex G
  let P := parametrizedFiberTransport pointedSpaceProjection x y
  let t := coherentColimitNativeIntervalVertex B H
  let q := pinchedHomLeftToIntervalMappingSpace x y
  let n := (coherentTotalMapNativeRepresentation F G
    (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))).1
  let m := (functorVertexEquiv _ _).symm (P.app (Opposite.op ⦋0⦌) t)
  have e := (pointedIntervalTransport_mapIso q).app n
  have hn : functorVertex (coherentTotalMapNativeFiberTransport F G
      (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))) =
      (pointedIntervalTransport q).map.app (Opposite.op ⦋0⦌) n :=
    (functorVertexEquiv _ _).apply_symm_apply _
  have hm : functorVertex m = P.app (Opposite.op ⦋0⦌) t :=
    (functorVertexEquiv _ _).apply_symm_apply _
  have et : FunctorIso m
      (edgeTransport pointedSpaceProjection (intervalMappingEdgeOfVertex t)) := by
    have h := parametrizedFiberTransport_at_edgeIso pointedSpaceProjection
      (intervalMappingEdgeOfVertex t)
    have ht : intervalMappingVertexOfEdge (intervalMappingEdgeOfVertex t) = t :=
      (intervalMappingEdgeVertexEquiv x y).apply_symm_apply t
    rw [ht] at h
    exact h
  exact eqToIso (congrArg SSet.HomotopyCategory.mk hn) ≪≫ e ≪≫
    (eqToIso (congrArg SSet.HomotopyCategory.mk hm)).symm ≪≫ et

/-- native 区間辺の Kan 値の射は、元の値比較を介して a6 の指定 native 輸送に整合する。 -/
def coherentColimitNativeIntervalLiftIso : FunctorIso
    ((pointedSpaceFiberValueEquivalence (coherentDiagramTotalCocone F).vertex).hom ≫
      (SSet.uliftFunctor.{u + 1, u}).map (coherentColimitNativeIntervalValue B H))
    (coherentTotalMapNativeFiberTransport F G
      (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H)) ≫
      (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom) :=
  spaceInfinityEdgeTransportValueIso
    (intervalMappingEdgeOfVertex (coherentColimitNativeIntervalVertex B H)) ≪≫
      ((coherentColimitNativeFiberEdgeIso B H).postcomp
        (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom).symm

end SerrePositivity.InfinityCategories.F2
