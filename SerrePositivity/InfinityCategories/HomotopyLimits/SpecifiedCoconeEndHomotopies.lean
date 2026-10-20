module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeNativeHomCoherence
public import SerrePositivity.InfinityCategories.HomotopyLimits.HomotopyEndpointTransport

/-!
概要：共通 end の元の HL・HR を、共通始点と公開した native 比較の始点で表示する。
方針：同じ射影円柱の終点の厳密な等式で表示変更する。
規約：元の円柱の raw な射を保持。使われ方：指定四辺の実際の関手正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (hB : IsColimitCone dB)
  (dC : JoinCocone (j ≫ p)) (hC : IsColimitCone dC) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "V" => specifiedCoconeCommonHomFamily hp p c hc dB dC y
local notation "UL" => coconePointHomFamily
  (partialColimitSpecifiedPathCocone hp p c hc dB dC) y ≫ cosliceRestrictionFiberMap p i y
local notation "UR" => specifiedCoconeRightHomRestriction hp p c hc dB dC y
local notation "PL" => specifiedCoconeLeftProjectedCylinder hp p c hc dB hB dC y
local notation "PR" => specifiedCoconeRightProjectedCylinder hp p c hc dB dC hC y

/-- 左の元の HL を、共通始点と左 native 比較の始点を持つ同じ円柱で表示する。 -/
def specifiedCoconeLeftEndHomotopy : SSet.Homotopy
    (V ≫ coconeMappingSpaceHomComparison c hc y)
    (UL ≫ coconeMappingSpaceHomComparison dB hB y ≫
      colimitAttachmentHomPrecomposition c hc f (i ≫ p) rfl dB y) :=
  homotopyEndpointTransport PL rfl
    (specifiedCoconeLeftRestrictionInitialHomFamily_projection hp p c hc dB hB dC y)

/-- 右の元の HR も同じ共通始点と右 native 比較の始点で表示する。 -/
def specifiedCoconeRightEndHomotopy : SSet.Homotopy
    (V ≫ coconeMappingSpaceHomComparison c hc y)
    (UR ≫ coconeMappingSpaceHomComparison dC hC y ≫ colimitAttachmentHomPrecomposition
      c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC y) :=
  homotopyEndpointTransport PR rfl
    (specifiedCoconeRightRestrictionInitialHomFamily_projection hp p c hc dB dC hC y)

/-- 左の表示変更後の円柱も、元の HL へ全 Hom の左制限を前合成した同じ raw な射。 -/
lemma specifiedCoconeLeftEndHomotopy_raw :
    (specifiedCoconeLeftEndHomotopy hp p c hc dB hB dC y).h =
      (functorHomotopyPrecomp (partialColimitHomEndLeftCylinder p y c hc dB hB) UL).h :=
  (homotopyEndpointTransport_raw PL rfl
    (specifiedCoconeLeftRestrictionInitialHomFamily_projection hp p c hc dB hB dC y)).trans
      (specifiedCoconeLeftProjectedCylinder_raw hp p c hc dB hB dC y)

/-- 右も、元の HR と全 Hom の右制限を全パラメータで保持する。 -/
lemma specifiedCoconeRightEndHomotopy_raw :
    (specifiedCoconeRightEndHomotopy hp p c hc dB dC hC y).h =
      (functorHomotopyPrecomp (partialColimitHomEndRightCylinder hp p y c hc dC hC) UR).h :=
  (homotopyEndpointTransport_raw PR rfl
    (specifiedCoconeRightRestrictionInitialHomFamily_projection hp p c hc dB dC hC y)).trans
      (specifiedCoconeRightProjectedCylinder_raw hp p c hc dB dC hC y)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
