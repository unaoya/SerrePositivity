module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeEndHomotopies
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.HomotopyPrecompInverseTransport

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
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone dB)
  (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone dC) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "V" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeCommonHomFamily hp p c hc dB dC y
local notation "UL" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC) y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p i y
local notation "UR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightHomRestriction hp p c hc dB dC y
local notation "HL" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitHomEndLeftCylinder p y c hc dB hB
local notation "HR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitHomEndRightCylinder hp p y c hc dC hC
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftEndHomotopy hp p c hc dB hB dC y
local notation "R" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightEndHomotopy hp p c hc dB dC hC y

/-- 左 path 成分が使う元の逆代表を、全 Hom の左制限で前合成した同じ円柱。 -/
def specifiedCoconeLeftEndInverseHomotopy : SSet.Homotopy
    (UL ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpaceHomComparison dB hB y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentHomPrecomposition c hc f (i ≫ p) rfl dB y)
    (V ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpaceHomComparison c hc y) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyPrecompInverseTransport HL UL L
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftEndHomotopy_raw hp p c hc dB hB dC y)

/-- 右も元の逆代表の選択を保ち、同じ共通成分を終点とする。 -/
def specifiedCoconeRightEndInverseHomotopy : SSet.Homotopy
    (UR ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpaceHomComparison dC hC y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentHomPrecomposition
      c hc g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC y)
    (V ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpaceHomComparison c hc y) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyPrecompInverseTransport HR UR R
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightEndHomotopy_raw hp p c hc dB dC hC y)

/-- 左の逆円柱の raw な射は、元の path end の逆代表の前合成そのもの。 -/
lemma specifiedCoconeLeftEndInverseHomotopy_raw :
    (specifiedCoconeLeftEndInverseHomotopy hp p c hc dB hB dC y).h =
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.simplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy HL).symm) UL).h :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyPrecompInverseTransport_raw HL UL L
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftEndHomotopy_raw hp p c hc dB hB dC y)

/-- 右の逆円柱も、元の同じ逆代表を全パラメータで保持する。 -/
lemma specifiedCoconeRightEndInverseHomotopy_raw :
    (specifiedCoconeRightEndInverseHomotopy hp p c hc dB dC hC y).h =
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.simplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy HR).symm) UR).h :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyPrecompInverseTransport_raw HR UR R
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightEndHomotopy_raw hp p c hc dB dC hC y)

/-- 左の元の逆代表の類は、共通端点で表示した元の順方向円柱の逆である。 -/
lemma specifiedCoconeLeftEndInverseHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (specifiedCoconeLeftEndInverseHomotopy hp p c hc dB hB dC y)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy L).inv :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyPrecompInverseTransport_hom HL UL L
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftEndHomotopy_raw hp p c hc dB hB dC y)

/-- 右も、同じ共通端点で表示した元の順方向円柱の逆の類を持つ。 -/
lemma specifiedCoconeRightEndInverseHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (specifiedCoconeRightEndInverseHomotopy hp p c hc dB dC hC y)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy R).inv :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyPrecompInverseTransport_hom HR UR R
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightEndHomotopy_raw hp p c hc dB dC hC y)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
