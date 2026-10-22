module

public import SerrePositivity.InfinityCategories.F2.Compact.CoconeLegPointTransfer
public import SerrePositivity.InfinityCategories.F2.Compact.CoconeLegPostcomposition

/-!
概要：元の指定余極限余錐の点回収を、元の同じ頂点表示と各脚の全辺へ正規化する。
方針：頂点の等式と全辺の厳密な一致を使い、指定点と実際の辺の作用を保持する。
規約：新しい余錐や脚を選ばない。使われ方：元の分類図式と coslice 輸送の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の頂点の表示と各脚の全辺の一致に沿って、同じ点回収を移す。 -/
lemma coconeLegPoint_reindex {I : SSet.{u + 1}} {D : I ⟶ SpaceInfinity.{u}}
    (c : JoinCocone D) (z : SpaceInfinity.{u} _⦋0⦌) (hz : c.vertex = z)
    (l : ∀ i : I _⦋0⦌, SpaceInfinity.{u}.Edge (D.app (Opposite.op ⦋0⦌) i) z)
    (hl : ∀ i, (coconeTransportLeg c i).edge = (l i).edge)
    (hc : HasCoconeLegPointRepresentatives c)
    (x : ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z).obj) _⦋0⦌) :
    ∃ i : I _⦋0⦌,
      ∃ v : ((SSet.uliftFunctor.{u + 1, u}).obj
        (spaceInfinityObject (D.app (Opposite.op ⦋0⦌) i)).obj) _⦋0⦌,
        SSet.π₀.mk (((SSet.uliftFunctor.{u + 1, u}).map
          (spaceInfinityEdgeValue (l i))).app (Opposite.op ⦋0⦌) v) = SSet.π₀.mk x := by
  subst z
  obtain ⟨i, v, hv⟩ := hc x
  have h : coconeTransportLeg c i = l i := SSet.Edge.ext (hl i)
  exact ⟨i, v, by simpa only [h] using hv⟩

/-- 指定余錐像の全ての点は、元の各脚の同じ後合成像の作用で成分まで回収できる。 -/
lemma mappedColimitCoconeLeg_point_representative {I : SSet.{u}} {B : SSet.{u + 1}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B)
    (G : B ⟶ SpaceInfinity.{u}) (c : JoinCocone D)
    (hc : IsColimitCone (mapJoinCocone G c))
    (x : ((SSet.uliftFunctor.{u + 1, u}).obj
      (spaceInfinityObject (G.app (Opposite.op ⦋0⦌) c.vertex)).obj) _⦋0⦌) :
    ∃ i : ((SSet.uliftFunctor.{u + 1, u}).obj I) _⦋0⦌,
      ∃ v : ((SSet.uliftFunctor.{u + 1, u}).obj
        (spaceInfinityObject (G.app (Opposite.op ⦋0⦌)
          (D.app (Opposite.op ⦋0⦌) i))).obj) _⦋0⦌,
        SSet.π₀.mk (((SSet.uliftFunctor.{u + 1, u}).map
          (spaceInfinityEdgeValue ((coconeTransportLeg c i).map G))).app (Opposite.op ⦋0⦌) v) =
            SSet.π₀.mk x :=
  coconeLegPoint_reindex (mapJoinCocone G c) _ (Ind.mapJoinCocone_vertex G c)
    (fun i => (coconeTransportLeg c i).map G) (coconeTransportLeg_post_edge G c)
    (colimitCoconeLeg_point_representative (D ≫ G) _ hc) x

end SerrePositivity.InfinityCategories.F2.Compact
