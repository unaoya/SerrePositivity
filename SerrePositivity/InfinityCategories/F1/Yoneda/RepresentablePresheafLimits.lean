module

public import SerrePositivity.InfinityCategories.HomotopyLimits.LiftedConePointedRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpacePointLimitDetection
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.SpaceLimitShapes

/-!
概要：元の表現可能前層による全極限錐の保存を、像の極限の存在から証明する。
方針：coslice の切断比較を元の native 全錐へ移し、一点からの切断で極限性を検出する。
規約：有限形状に限定しない。像の極限の存在は明示し、一般の小極限の存在と区別する。
使われ方：F1-4、HTT 5.1.3.2 の表現可能関手の極限保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {K C : SSet.{u}} [Quasicategory C] {D : K ⟶ C.op}
  (c : JoinCone D) (y : C _⦋0⦌)

/-- 元の表現可能前層の像に極限があれば、同じ全極限錐そのものを保存する。 -/
lemma representablePresheafInfinity_isLimit_of_hasLimit (hc : IsLimitCone c)
    (hD : HasLimit ((SSet.uliftFunctor.{u + 1, u}).map D ≫
      representablePresheafInfinity y)) :
    IsLimitCone (mapJoinCone (representablePresheafInfinity y)
      (JoinCone.ulift.{u, u + 1} c)) :=
  HomotopyLimits.spaceCone_isLimit_of_pointRestriction_of_hasLimit _ hD
    (HomotopyLimits.representableNativeConePointedRestriction_isQCatEquivalence c hc y)

/-- 元の形状の空間値極限が存在すれば、表現可能前層は全極限錐を保存する。 -/
lemma representablePresheafInfinity_isLimit_of_spaceLimitsOfShape (hc : IsLimitCone c)
    (hK : F2.HasSpaceLimitsOfShape K) :
    IsLimitCone (mapJoinCone (representablePresheafInfinity y)
      (JoinCone.ulift.{u, u + 1} c)) :=
  representablePresheafInfinity_isLimit_of_hasLimit c y hc (hK _)

end SerrePositivity.InfinityCategories
