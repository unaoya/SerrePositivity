module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.CoconeLegPointTransfer
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.CoconeLegPostcomposition

/-!
概要：元の指定余極限余錐の点回収を、元の同じ頂点表示と各脚の全辺へ正規化する。
方針：頂点の等式と全辺の厳密な一致を使い、指定点と実際の辺の作用を保持する。
規約：新しい余錐や脚を選ばない。使われ方：元の分類図式と coslice 輸送の照合。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 元の頂点の表示と各脚の全辺の一致に沿って、同じ点回収を移す。 -/
lemma coconeLegPoint_reindex {I : SSet.{u + 1}} {D : I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) (hz : c.vertex = z)
    (l : ∀ i : I _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}.Edge (D.app (Opposite.op ⦋0⦌) i) z)
    (hl : ∀ i, (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c i).edge = (l i).edge)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasCoconeLegPointRepresentatives c)
    (x : ((SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject z).obj) _⦋0⦌) :
    ∃ i : I _⦋0⦌,
      ∃ v : ((SSet.uliftFunctor.{u + 1, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (D.app (Opposite.op ⦋0⦌) i)).obj) _⦋0⦌,
        SSet.π₀.mk (((SSet.uliftFunctor.{u + 1, u}).map
          (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (l i))).app (Opposite.op ⦋0⦌) v) = SSet.π₀.mk x := by
  subst z
  obtain ⟨i, v, hv⟩ := hc x
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c i = l i := SSet.Edge.ext (hl i)
  exact ⟨i, v, by simpa only [h] using hv⟩

/-- 指定余錐像の全ての点は、元の各脚の同じ後合成像の作用で成分まで回収できる。 -/
lemma mappedColimitCoconeLeg_point_representative {I : SSet.{u}} {B : SSet.{u + 1}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B)
    (G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G c))
    (x : ((SSet.uliftFunctor.{u + 1, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (G.app (Opposite.op ⦋0⦌) c.vertex)).obj) _⦋0⦌) :
    ∃ i : ((SSet.uliftFunctor.{u + 1, u}).obj I) _⦋0⦌,
      ∃ v : ((SSet.uliftFunctor.{u + 1, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (G.app (Opposite.op ⦋0⦌)
          (D.app (Opposite.op ⦋0⦌) i))).obj) _⦋0⦌,
        SSet.π₀.mk (((SSet.uliftFunctor.{u + 1, u}).map
          (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c i).map G))).app (Opposite.op ⦋0⦌) v) =
            SSet.π₀.mk x :=
  coconeLegPoint_reindex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G c) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex G c)
    (fun i => (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c i).map G) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg_post_edge G c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.colimitCoconeLeg_point_representative (D ≫ G) _ hc) x

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
