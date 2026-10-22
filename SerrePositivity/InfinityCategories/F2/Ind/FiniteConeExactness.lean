module

public import SerrePositivity.InfinityCategories.F2.Ind.ConePresheafRestriction
public import SerrePositivity.InfinityCategories.F2.Ind.FiniteLimitExchangeInput
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredClosure
public import SerrePositivity.InfinityCategories.F2.Ind.CoconeTransformationPointPost
public import SerrePositivity.InfinityCategories.F2.VertexConeIsoTransport

/-!
概要：Indκ の全前層は、交換定理を入力した形状の元の極限全錐を保存する。
方針：表現可能前層の保存性を、全錐の制限族の同型と κ-filtered 閉包へ移す。
規約：交換定理は明示引数。この定理でその入力の存在を主張しない。
使われ方：Ind の表現可能な有限余極限錐の普遍性と、安定性への条件付き経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 全錐を保つ一般 coherent 交換から、最小 κ-filtered 閉包の全頂点での極限性を得る。 -/
lemma indVertex_cone_isLimit_of_exchange (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    {K C : SSet.{u}} [Quasicategory C] {D : K ⟶ C.op}
    (c : JoinCone D) (hc : IsLimitCone c) (hK : CoherentFilteredLimitExchangeShape K)
    {v : (PresheafInfinity C) _⦋0⦌} (hv : IsIndVertex κ C v) :
    IsLimitCone (functorVertexCone ((conePresheafRestriction c).app (Opposite.op ⦋0⦌) v)) := by
  apply hv (fun w => IsLimitCone
    (functorVertexCone ((conePresheafRestriction c).app (Opposite.op ⦋0⦌) w)))
  · intro y
    rw [yonedaInfinityMap_vertex]
    exact (conePresheafRestriction_isLimit_iff c (representablePresheafInfinity y)).mpr
      (representablePresheafInfinity_isLimit c hc y)
  · intro a b e ha
    exact (isLimitCone_functorVertexCone_iff_of_vertexIso
      (e.map (conePresheafRestriction c))).mp ha
  · intro I hI hFiltered p d hd hp
    let : IsFilteredInfinity I := isFilteredInfinity_of_isKappaFiltered hκ I
    have ht := hK I (p ≫ conePresheafRestriction c)
      (mapJoinCocone (conePresheafRestriction c) d)
      (conePresheafRestriction_isPointwiseColimit c p d hd) hp
    rw [mapJoinCocone_vertex] at ht
    exact ht

/-- 明示の有限交換入力から、元の Ind 前層による同じ有限全錐の極限保存を得る。 -/
lemma indPresheaf_finiteCone_isLimit (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hex : IndFiniteLimitExchangeInput.{u}) {K C : SSet.{u}} [K.Finite]
    [Quasicategory C] {D : K ⟶ C.op} (c : JoinCone D) (hc : IsLimitCone c)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
    (hF : IsIndVertex κ C (functorVertex F)) :
    IsLimitCone (mapJoinCone F (JoinCone.ulift.{u, u + 1} c)) :=
  (conePresheafRestriction_isLimit_iff c F).mp
    (indVertex_cone_isLimit_of_exchange κ hκ c hc (hex.exchange K) hF)

end SerrePositivity.InfinityCategories.F2.Ind
