module

public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentablePresheafLimits
public import SerrePositivity.InfinityCategories.F1.Coherent.SpaceSmallLimits

/-!
概要：表現可能前層による小さい極限の保存から、像の存在条件を解消する。
方針：同じ元の像の図式に一般の coherent 小極限の存在を入力する。
規約：有限性・離散性は要求せず、元の極限全錐そのものを保存する。
使われ方：F1-4、HTT 5.1.3.2、表現可能関手による極限の特徴づけ。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の表現可能前層は、任意の小さい形状の同じ native な極限全錐を保存する。 -/
lemma representablePresheafInfinity_isLimit {K C : SSet.{u}} [Quasicategory C]
    {D : K ⟶ C.op} (c : JoinCone D) (hc : IsLimitCone c) (y : C _⦋0⦌) :
    IsLimitCone (mapJoinCone (representablePresheafInfinity y)
      (JoinCone.ulift.{u, u + 1} c)) :=
  representablePresheafInfinity_isLimit_of_hasLimit c y hc
    (hasLimit_coherentSpaceDiagram ((SSet.uliftFunctor.{u + 1, u}).map D ≫
      representablePresheafInfinity y))

end SerrePositivity.InfinityCategories
