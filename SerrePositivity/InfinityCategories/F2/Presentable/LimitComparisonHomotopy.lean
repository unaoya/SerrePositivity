module

public import SerrePositivity.InfinityCategories.F2.Presentable.LimitComparisonReflection
public import SerrePositivity.InfinityCategories.F2.ColimitHomotopyPointwise

/-!
概要：同じ二つの普遍錐間の全比較は、基底の各成分が可逆なら全体が可逆。
方針：元の比較辺を普遍錐の全部分圏へ戻し、充満忠実な射影で可逆性を反映する。
規約：元の全錐と全ホモトピーを保持。全形状の極限存在は不要。
使われ方：全 Hom 比較の極限頂点での可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 基底への制限が可逆な、同じ元の普遍錐間の比較辺は可逆。 -/
lemma limitComparison_isInvertible_of_restriction {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (c : JoinCone p) (d : JoinCone q)
    (hc : IsLimitCone c) (hd : IsLimitCone d) (H : SSet.Homotopy c.val d.val)
    (hH : IsIso ((hoFunctor.map (coneRestriction K X)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)))) :
    IsInvertibleEdge (functorEdgeOfSimplicialHomotopy H) := by
  have : Quasicategory (relativeTerminalVertices (coneRestriction K X) : SSet.{u}) :=
    fullSubcomplexOnVertices_quasicategory _ _
  let i := (relativeTerminalVertices (coneRestriction K X)).ι
  let v := SSet.Truncated.HomotopyCategory.homMk (limitComparisonEdge c d hc hd H)
  let F := (hoFunctor.map (relativeTerminalProjection (coneRestriction K X))).toFunctor
  have hF := (relativeTerminalProjection_isFullyFaithful (coneRestriction K X)).toHoFullyFaithful
  let : F.Full := hF.full
  let : F.Faithful := hF.faithful
  have hv : (hoFunctor.map i).toFunctor.map v =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) :=
    congrArg SSet.Truncated.HomotopyCategory.homMk (limitComparisonEdge_map c d hc hd H)
  have hFv : IsIso (F.map v) := by
    change IsIso ((hoFunctor.map (coneRestriction K X)).toFunctor.map
      ((hoFunctor.map i).toFunctor.map v))
    rw [hv]
    exact hH
  let := hFv
  have hvIso : IsIso v := isIso_of_reflects_iso v F
  let := hvIso
  have h := (hoFunctor.map i).toFunctor.map_isIso v
  rw [hv] at h
  exact h

/-- 元の基底各点で可逆な同じ普遍錐の全比較は可逆。 -/
lemma limitComparison_isInvertible_of_pointwise {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (c : JoinCone p) (d : JoinCone q)
    (hc : IsLimitCone c) (hd : IsLimitCone d) (H : SSet.Homotopy c.val d.val)
    (hH : ∀ k : K _⦋0⦌, IsInvertibleEdge (simplicialHomotopyVertexEdge H
      ((joinInr Δ[0] K).app (Opposite.op ⦋0⦌) k)).toTruncated) :
    IsInvertibleEdge (functorEdgeOfSimplicialHomotopy H) := by
  apply limitComparison_isInvertible_of_restriction c d hc hd H
  change IsIso ((hoFunctor.map ((pre (joinInr Δ[0] K)).app X)).toFunctor.map
    (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)))
  rw [homMk_functorEdge_precomp]
  apply functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise
  intro k
  exact (isInvertibleEdge_congr (homotopyVertexEdge_precomp (joinInr Δ[0] K) H k)).mpr (hH k)

end SerrePositivity.InfinityCategories.F2.Presentable
