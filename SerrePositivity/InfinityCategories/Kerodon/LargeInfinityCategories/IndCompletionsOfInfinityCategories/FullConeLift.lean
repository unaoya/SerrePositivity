module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PresheafSubcategory
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FullSubcomplexConeLift
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FullSubcomplexLimitReflection

/-!
概要：元の Ind 図式の前層内の全錐を持ち上げ、同じ錐の極限性を反映する。
方針：許可された全部分複体の全錐持ち上げと極限反映を適用する。
規約：元の全図式・全錐を厳密に保持し、既存の深層ファイルは変更しない。
使われ方：filtered 全錐族の余極限から Ind 内の有限極限を回収する。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {K : SSet.{u + 1}} (D : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)

/-- 前層内の指定全錐は、頂点の所属だけで同じ Ind 図式の全錐へ持ち上がる。 -/
def indFullConeLift (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C))
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C c.vertex) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone D :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fullSubcomplexConeLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C) D c hc

/-- 持ち上げた全錐の包含像は元の指定全錐そのもの。 -/
lemma indFullConeLift_inclusion (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C))
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C c.vertex) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C) (indFullConeLift κ D c hc) = c :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fullSubcomplexConeLift_inclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C) D c hc

/-- 全部分包含は任意の形状の元の全錐の極限性を反映する。 -/
lemma ind_isLimit_of_inclusion (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone D)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C) c)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.isLimitCone_of_fullSubcomplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C) c hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
