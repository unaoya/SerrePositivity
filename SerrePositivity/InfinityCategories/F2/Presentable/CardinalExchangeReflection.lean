module

public import SerrePositivity.InfinityCategories.F2.Presentable.CardinalExchangeShape
public import SerrePositivity.InfinityCategories.F2.Compact.ExchangeCoconeCompletion

/-!
概要：同じ μ-filtered な全極限錐族で、底図式の点ごとの余極限性から全錐の余極限性を反映する。
方針：同じ全族の点ごとの補完を作り、実証済みの形状交換と全錐比較の可逆性を使う。
規約：N の有限交換入力を仮定せず、元の μ-filtered 条件と指定全余錐を保持する。
使われ方：元の指定余極限頂点の μ-compact 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open Compact HomotopyLimits

/-- 元の μ-filtered な全錐族の底部分の余極限性は、同じ全錐の全評価の余極限性を反映する。 -/
lemma pointwiseColimit_of_cardinalExchange {μ : Cardinal.{u}} {K B : SSet.{u}}
    [Quasicategory B] [IsKappaFiltered μ B] (hK : CardinalFilteredLimitExchangeShape μ K)
    (p : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶
      (ihom (join (Δ[0] : SSet.{u + 1})
        ((SSet.uliftFunctor.{u + 1, u}).obj K))).obj SpaceInfinity.{u})
    (hp : ∀ b : B _⦋0⦌, IsLimitCone (functorVertexCone
      (p.app (Opposite.op ⦋0⦌) (ULift.up b))))
    (c : JoinCocone p) (hc : IsLimitCone (functorVertexCone c.vertex))
    (hr : IsPointwiseColimitCone (mapJoinCocone
      (coneRestriction ((SSet.uliftFunctor.{u + 1, u}).obj K) SpaceInfinity.{u}) c)) :
    IsPointwiseColimitCone c := by
  let R := coneRestriction ((SSet.uliftFunctor.{u + 1, u}).obj K) SpaceInfinity.{u}
  obtain ⟨d, hd, hdpoint⟩ := exists_spaceFunctor_pointwiseColimit p
  have hdlim : IsLimitCone (functorVertexCone d.vertex) := hK B p d hdpoint hp
  have hdr : IsPointwiseColimitCone (mapJoinCocone R d) :=
    hdpoint.reindex (joinInr (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K))
  have hdR : IsColimitCone (mapJoinCocone R d) := isColimitCone_functor_of_pointwise _ hdr
  have hcR : IsColimitCone (mapJoinCocone R c) := isColimitCone_functor_of_pointwise _ hr
  obtain ⟨e₀⟩ := IsInitialVertex.nonempty_edge (X := sliceUnder p) hd c
  let e := SSet.Edge.ofTruncated (X := sliceUnder p) e₀
  have hbase := colimitComparisonApex_map_isInvertible R hdR hcR e
  have hfull := limitConeEdge_reflects_invertible hdlim hc (colimitComparisonApexEdge e) hbase
  have he : IsInvertibleEdge (X := sliceUnder p) e :=
    leftFibration_reflects_invertibleEdge (sliceUnderProjection p) e.toTruncated hfull
  have : IsIso (SSet.HomotopyCategory.homMk e) := he
  let i : VertexIso (X := sliceUnder p) d c := asIso (SSet.HomotopyCategory.homMk e)
  intro l
  exact (hdpoint l).of_functorIso
    ((coconeFunctorIsoOfVertexIso d c i).postcomp (evaluateFunctorAt l))

end SerrePositivity.InfinityCategories.F2.Presentable
