module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeEndHomotopies
public import SerrePositivity.InfinityCategories.HomotopyLimits.HomotopyPrecompInverseTransport

/-!
概要：path end の自然変換が使う元の HL・HR の逆代表を、共通成分の端点で表示する。
方針：逆を選んだ後の前合成を保持し、順方向円柱の raw な式で端点を揃える。
規約：逆代表の選択順を固定。使われ方：共通 end 内の指定逆経路の正方形。
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
local notation "HL" => partialColimitHomEndLeftCylinder p y c hc dB hB
local notation "HR" => partialColimitHomEndRightCylinder hp p y c hc dC hC
local notation "L" => specifiedCoconeLeftEndHomotopy hp p c hc dB hB dC y
local notation "R" => specifiedCoconeRightEndHomotopy hp p c hc dB dC hC y

/-- 左 path 成分が使う元の逆代表を、全 Hom の左制限で前合成した同じ円柱。 -/
def specifiedCoconeLeftEndInverseHomotopy : SSet.Homotopy
    (UL ≫ coconeMappingSpaceHomComparison dB hB y ≫
      colimitAttachmentHomPrecomposition c hc f (i ≫ p) rfl dB y)
    (V ≫ coconeMappingSpaceHomComparison c hc y) :=
  homotopyPrecompInverseTransport HL UL L
    (specifiedCoconeLeftEndHomotopy_raw hp p c hc dB hB dC y)

/-- 右も元の逆代表の選択を保ち、同じ共通成分を終点とする。 -/
def specifiedCoconeRightEndInverseHomotopy : SSet.Homotopy
    (UR ≫ coconeMappingSpaceHomComparison dC hC y ≫ colimitAttachmentHomPrecomposition
      c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC y)
    (V ≫ coconeMappingSpaceHomComparison c hc y) :=
  homotopyPrecompInverseTransport HR UR R
    (specifiedCoconeRightEndHomotopy_raw hp p c hc dB dC hC y)

/-- 左の逆円柱の raw な射は、元の path end の逆代表の前合成そのもの。 -/
lemma specifiedCoconeLeftEndInverseHomotopy_raw :
    (specifiedCoconeLeftEndInverseHomotopy hp p c hc dB hB dC y).h =
      (functorHomotopyPrecomp (FunctorIso.simplicialHomotopy
        (functorIsoOfSimplicialHomotopy HL).symm) UL).h :=
  homotopyPrecompInverseTransport_raw HL UL L
    (specifiedCoconeLeftEndHomotopy_raw hp p c hc dB hB dC y)

/-- 右の逆円柱も、元の同じ逆代表を全パラメータで保持する。 -/
lemma specifiedCoconeRightEndInverseHomotopy_raw :
    (specifiedCoconeRightEndInverseHomotopy hp p c hc dB dC hC y).h =
      (functorHomotopyPrecomp (FunctorIso.simplicialHomotopy
        (functorIsoOfSimplicialHomotopy HR).symm) UR).h :=
  homotopyPrecompInverseTransport_raw HR UR R
    (specifiedCoconeRightEndHomotopy_raw hp p c hc dB dC hC y)

/-- 左の元の逆代表の類は、共通端点で表示した元の順方向円柱の逆である。 -/
lemma specifiedCoconeLeftEndInverseHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (specifiedCoconeLeftEndInverseHomotopy hp p c hc dB hB dC y)) =
      (functorIsoOfSimplicialHomotopy L).inv :=
  homotopyPrecompInverseTransport_hom HL UL L
    (specifiedCoconeLeftEndHomotopy_raw hp p c hc dB hB dC y)

/-- 右も、同じ共通端点で表示した元の順方向円柱の逆の類を持つ。 -/
lemma specifiedCoconeRightEndInverseHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (specifiedCoconeRightEndInverseHomotopy hp p c hc dB dC hC y)) =
      (functorIsoOfSimplicialHomotopy R).inv :=
  homotopyPrecompInverseTransport_hom HR UR R
    (specifiedCoconeRightEndHomotopy_raw hp p c hc dB dC hC y)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
