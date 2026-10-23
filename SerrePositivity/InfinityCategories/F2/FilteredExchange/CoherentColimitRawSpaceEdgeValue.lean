module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedSpaceEdgeValueIso
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawTransportPointPrism
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexTriangle

/-!
概要：元の余極限二単体の三実辺に、元の全 Hom 成分による実輸送の値比較を適用する。
方針：元の余錐両頂点で同じ実辺を保持し、同じ元の二単体の三面へ厳密に回収する。
規約：元の三辺・全二単体・指定成分を保持。使われ方：普遍三角形残余と元の指定 path の照合。
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
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : SSet.Homotopy F G)

/-- 元の余錐両頂点を実両端に持つ、同じ元の余極限指定辺。 -/
def coherentColimitRawSpaceEdge : SpaceInfinity.Edge
    (coherentDiagramTotalCocone F).vertex (coherentDiagramTotalCocone G).vertex :=
  ⟨(coherentColimitFunctorEdge B a).edge,
    (coherentColimitFunctorEdge B a).src_eq.trans (coherentDiagramTotalCocone_vertex F).symm,
    (coherentColimitFunctorEdge B a).tgt_eq.trans (coherentDiagramTotalCocone_vertex G).symm⟩

/-- 同じ実辺の区間頂点は、元の raw 普遍輸送で使う同じ指定頂点そのもの。 -/
lemma coherentColimitRawSpaceEdge_interval :
    intervalMappingVertexOfEdge (coherentColimitRawSpaceEdge B a) =
      coherentColimitRawIntervalVertex B a := rfl

/-- 同じ raw 余極限辺の実輸送を、元の全 Hom の指定成分で同じ Kan 射へ比較する。 -/
def coherentColimitRawSpaceEdgeValueIso :
    FunctorIso (coherentColimitRawFiberTransport B a ≫
      pointedFiberValueTo (spaceEdge_target_to_object (coherentColimitRawSpaceEdge B a)))
      (pointedFiberValueTo (spaceEdge_source_to_object (coherentColimitRawSpaceEdge B a)) ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (coherentEdgeHom (coherentColimitFunctorEdge B a).edge)) :=
  pointedSpaceEdgeValueIso (coherentColimitRawSpaceEdge B a)

variable {J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {b : SSet.Homotopy G J} {d : SSet.Homotopy F J} (T : FunctorCompositionTriangle a b d)

/-- 第一辺の値比較は、元の同じ余極限二単体の実第一辺に適用される。 -/
lemma coherentColimitRawSpaceEdge_first :
    (coherentColimitRawSpaceEdge B a).edge = SpaceInfinity.δ 2 (coherentColimitApexTriangle B T) :=
  (coherentColimitApexTriangle_first B T).symm

/-- 最後辺の値比較も、元の同じ余極限二単体の実最後辺に適用される。 -/
lemma coherentColimitRawSpaceEdge_last :
    (coherentColimitRawSpaceEdge B b).edge = SpaceInfinity.δ 0 (coherentColimitApexTriangle B T) :=
  (coherentColimitApexTriangle_last B T).symm

/-- 長辺の値比較も、元の同じ余極限二単体の実長辺に適用される。 -/
lemma coherentColimitRawSpaceEdge_long :
    (coherentColimitRawSpaceEdge B d).edge = SpaceInfinity.δ 1 (coherentColimitApexTriangle B T) :=
  (coherentColimitApexTriangle_long B T).symm

end SerrePositivity.InfinityCategories.F2
