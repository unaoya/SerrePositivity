module
public import SerrePositivity.InfinityCategories.HomotopyLimits.CatInfinity.FunctorCoconePointwiseCriterion

public import SerrePositivity.InfinityCategories.F2.Compact.LimitConeEdgeReflection
public import SerrePositivity.InfinityCategories.F2.Compact.ColimitComparisonApex
public import SerrePositivity.InfinityCategories.F1.Filtered.CoherentFilteredLimitExchange
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTotalColimit
public import SerrePositivity.InfinityCategories.HomotopyLimits.CatInfinity.FunctorColimitConeExistence
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorCoconeReindex
public import SerrePositivity.InfinityCategories.F1.SquareFunctorTransport

/-!
概要：極限錐の族の指定余錐は、底図式で点ごとに余極限なら全錐でも点ごとに余極限。
方針：実際の点ごとの余極限補完へ交換定理を適用し、元の全比較辺の可逆性を反映する。
規約：交換定理を明示し、元の指定余錐とその全比較を保持する。
使われ方：全 Hom の極限表示から compact 対象の有限余極限閉性へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の小さい空間値図式の族には、同じ全図式上の点ごとの余極限補完が存在する。 -/
lemma exists_spaceFunctor_pointwiseColimit {B : SSet.{u}} {L : SSet.{u + 1}}
    (p : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ (ihom L).obj SpaceInfinity.{u}) :
    ∃ d : JoinCocone p, IsColimitCone d ∧ IsPointwiseColimitCone d := by
  obtain ⟨d, hd, hp⟩ := exists_colimitCone_functor_of_pointwise p
    (fun l => hasColimit_coherentSpaceDiagram (p ≫ evaluateFunctorAt l))
  exact ⟨d, hd, hp⟩

/-- 同じ全極限錐の指定余錐で、底図式の点ごとの余極限性から全錐の余極限性を反映。 -/
lemma pointwiseColimit_of_limit_exchange {K B : SSet.{u}}
    [Quasicategory B] [IsFilteredInfinity B] (hK : CoherentFilteredLimitExchangeShape K)
    (p : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶
      (ihom (join (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K))).obj
        SpaceInfinity.{u})
    (hp : ∀ b : B _⦋0⦌,
      IsLimitCone (functorVertexCone (p.app (Opposite.op ⦋0⦌) (ULift.up b))))
    (c : JoinCocone p) (hc : IsLimitCone (functorVertexCone c.vertex))
    (hr : IsPointwiseColimitCone (mapJoinCocone
      (coneRestriction ((SSet.uliftFunctor.{u + 1, u}).obj K) SpaceInfinity.{u}) c)) :
    IsPointwiseColimitCone c := by
  let R := coneRestriction ((SSet.uliftFunctor.{u + 1, u}).obj K) SpaceInfinity.{u}
  obtain ⟨d, hd, hdpoint⟩ := exists_spaceFunctor_pointwiseColimit p
  have hdlim : IsLimitCone (functorVertexCone d.vertex) := hK B p d hdpoint hp
  have hdr : IsPointwiseColimitCone (mapJoinCocone R d) :=
    hdpoint.reindex (joinInr (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K))
  have hdR : IsColimitCone (mapJoinCocone R d) :=
    isColimitCone_functor_of_pointwise _ hdr
  have hcR : IsColimitCone (mapJoinCocone R c) :=
    isColimitCone_functor_of_pointwise _ hr
  obtain ⟨e₀⟩ := IsInitialVertex.nonempty_edge (X := sliceUnder p) hd c
  let e := SSet.Edge.ofTruncated (X := sliceUnder p) e₀
  have hbase := colimitComparisonApex_map_isInvertible R hdR hcR e
  have hfull := limitConeEdge_reflects_invertible hdlim hc
    (colimitComparisonApexEdge e) hbase
  have he : IsInvertibleEdge (X := sliceUnder p) e :=
    leftFibration_reflects_invertibleEdge (sliceUnderProjection p) e.toTruncated hfull
  have : IsIso (SSet.HomotopyCategory.homMk e) := he
  let i : VertexIso (X := sliceUnder p) d c := asIso (SSet.HomotopyCategory.homMk e)
  intro l
  exact (hdpoint l).of_functorIso
    ((coconeFunctorIsoOfVertexIso d c i).postcomp (evaluateFunctorAt l))

end SerrePositivity.InfinityCategories.F2.Compact
