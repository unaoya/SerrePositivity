module

public import SerrePositivity.InfinityCategories.F2.Ind.PresheafSubcategory
public import SerrePositivity.InfinityCategories.HomotopyLimits.FullSubcomplexConeLift
public import SerrePositivity.InfinityCategories.HomotopyLimits.FullSubcomplexLimitReflection

/-!
概要：元の Ind 図式の前層内の全錐を持ち上げ、同じ錐の極限性を反映する。
方針：許可された全部分複体の全錐持ち上げと極限反映を適用する。
規約：元の全図式・全錐を厳密に保持し、既存の深層ファイルは変更しない。
使われ方：filtered 全錐族の余極限から Ind 内の有限極限を回収する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {K : SSet.{u + 1}} (D : K ⟶ IndInfinity κ C)

/-- 前層内の指定全錐は、頂点の所属だけで同じ Ind 図式の全錐へ持ち上がる。 -/
def indFullConeLift (c : JoinCone (D ≫ indInclusionPresheaf κ C))
    (hc : IsIndVertex κ C c.vertex) : JoinCone D :=
  HomotopyLimits.fullSubcomplexConeLift (IsIndVertex κ C) D c hc

/-- 持ち上げた全錐の包含像は元の指定全錐そのもの。 -/
lemma indFullConeLift_inclusion (c : JoinCone (D ≫ indInclusionPresheaf κ C))
    (hc : IsIndVertex κ C c.vertex) :
    mapJoinCone (indInclusionPresheaf κ C) (indFullConeLift κ D c hc) = c :=
  HomotopyLimits.fullSubcomplexConeLift_inclusion (IsIndVertex κ C) D c hc

/-- 全部分包含は任意の形状の元の全錐の極限性を反映する。 -/
lemma ind_isLimit_of_inclusion (c : JoinCone D)
    (hc : IsLimitCone (mapJoinCone (indInclusionPresheaf κ C) c)) : IsLimitCone c :=
  HomotopyLimits.isLimitCone_of_fullSubcomplex (IsIndVertex κ C) c hc

end SerrePositivity.InfinityCategories.F2.Ind
