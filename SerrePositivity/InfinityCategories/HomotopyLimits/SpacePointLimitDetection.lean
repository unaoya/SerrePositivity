module

public import SerrePositivity.InfinityCategories.HomotopyLimits.NativeConeFamilyEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.RightFibrationInvertibleReflection
public import SerrePositivity.InfinityCategories.F1.CoherentKanInvertible
public import SerrePositivity.InfinityCategories.Core.TerminalUniqueness

/-!
概要：既存の極限錐を持つ空間値図式では、一点からの切断制限が元の錐の極限性を検出する。
方針：元の極限錐への比較辺の頂点輸送を検出し、元の slice の辺の可逆性を反映する。
規約：元の候補錐を保持し、比較錐の存在を証明とは区別する。
使われ方：元の Yoneda の有限積保存で、存在する空間積錐と比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 極限の存在が与えられた元の空間値図式では、一点からの切断制限で元の極限性を検出。 -/
lemma spaceCone_isLimit_of_pointRestriction_of_hasLimit {K : SSet.{u + 1}}
    {D : K ⟶ SpaceInfinity.{u}} (c : JoinCone D) (hD : HasLimit D)
    (hc : IsQCatEquivalence (coneSectionRestriction c pointSpaceVertex)) : IsLimitCone c := by
  obtain ⟨d, hd⟩ := hD
  obtain ⟨e₀⟩ := hd.nonempty_edge c
  let e : (sliceOver D).Edge c d := SSet.Edge.ofTruncated e₀
  have hd' := ((isLimitCone_iff_coneSectionRestriction_homotopyEquivalence d).mp hd
    pointSpaceVertex).isQCatEquivalence
  have ht := coneComparisonApexTransport_isQCatEquivalence c d pointSpaceVertex
    (nativeConeFunctorEdge e) (nativeConeFunctorEdge_restriction_isInvertible e) hc hd'
  have hi := pointedSpaceEdge_isInvertible_of_transport_isQCatEquivalence
    ((nativeConeFunctorEdge e).map (evaluateFunctorAt (joinApexVertex K))) ht
  have hp : IsInvertibleEdge (e.map (sliceOverProjection D)) :=
    (isInvertibleEdge_congr (nativeConeFunctorEdge_apex e)).mp hi
  have he := rightFibration_reflects_isInvertibleEdge (sliceOverProjection D) e hp
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk e₀) := he
  exact hd.of_vertexIso (asIso (SSet.Truncated.HomotopyCategory.homMk e₀)).symm

/-- 同じ元の図式に極限があれば、一点からの制限は元の錐の極限性と同値。 -/
lemma spaceCone_isLimit_iff_pointRestriction_of_hasLimit {K : SSet.{u + 1}}
    {D : K ⟶ SpaceInfinity.{u}} (c : JoinCone D) (hD : HasLimit D) :
    IsLimitCone c ↔ IsQCatEquivalence (coneSectionRestriction c pointSpaceVertex) :=
  ⟨fun hc ↦ ((isLimitCone_iff_coneSectionRestriction_homotopyEquivalence c).mp hc
    pointSpaceVertex).isQCatEquivalence,
    spaceCone_isLimit_of_pointRestriction_of_hasLimit c hD⟩

end SerrePositivity.InfinityCategories.HomotopyLimits
