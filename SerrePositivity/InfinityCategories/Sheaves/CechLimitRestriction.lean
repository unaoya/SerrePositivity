module

public import SerrePositivity.InfinityCategories.Sheaves.CechShapeCofinality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalLimitTransfer

/-!
概要：弱終対象の元の Čech 形状で、指定極限錐と極限の存在を判定する。
方針：検証した元の形状の left cofinality を、既存の指定錐の制限定理へ渡す。
使われ方：HTT 4.1.3.1、Kerodon §7.2（Tag 02MZ）、BS Construction 4.18 脚注10。
規約：小さい site と大きい site とも同じ元の錐の頂点を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
namespace SerrePositivity.InfinityCategories.Sheaves

/-- 元の全錐が極限であることと、同じ Čech 制限錐の極限性は同値。 -/
theorem isLimitCone_iff_restrict_cech {C : Type u} [SmallCategory C]
    {E : SSet.{u + 1}} [Quasicategory E] {U : C}
    (hU : CategoryTheory.IsWeaklyTerminal U) (d : CategoryTheory.CechNerveData U)
    (F : Presheaf C E) (c : JoinCone F) :
    IsLimitCone c ↔ IsLimitCone (restrictJoinCone c (cechShape d)) :=
  isLimitCone_iff_restrict_of_leftCofinal _ (cechShape_isLeftCofinal d hU) F c

/-- 全図式の極限の存在は、元の Čech 図式の極限の存在と同値。 -/
theorem hasLimit_iff_cech {C : Type u} [SmallCategory C]
    {E : SSet.{u + 1}} [Quasicategory E] {U : C}
    (hU : CategoryTheory.IsWeaklyTerminal U) (d : CategoryTheory.CechNerveData U)
    (F : Presheaf C E) : HasLimit F ↔ HasLimit (cechShape d ≫ F) :=
  hasLimit_iff_restrict_of_leftCofinal _ (cechShape_isLeftCofinal d hU) F

/-- 大きい site の元の全錐も、小さい Čech 形状の同じ制限錐で判定する。 -/
theorem isLimitCone_iff_restrict_cech_large {C : Type (u + 1)} [Category.{u} C]
    {E : SSet.{u + 1}} [Quasicategory E] {U : C}
    (hU : CategoryTheory.IsWeaklyTerminal U) (d : CategoryTheory.CechNerveData U)
    (F : nerve Cᵒᵖ ⟶ E) (c : JoinCone F) :
    IsLimitCone c ↔ IsLimitCone (restrictJoinCone c (cechShapeLarge d)) :=
  isLimitCone_iff_restrict_of_leftCofinal _ (cechShapeLarge_isLeftCofinal d hU) F c

/-- 大きい site でも、小さい Čech 形状で極限の存在を判定する。 -/
theorem hasLimit_iff_cech_large {C : Type (u + 1)} [Category.{u} C]
    {E : SSet.{u + 1}} [Quasicategory E] {U : C}
    (hU : CategoryTheory.IsWeaklyTerminal U) (d : CategoryTheory.CechNerveData U)
    (F : nerve Cᵒᵖ ⟶ E) : HasLimit F ↔ HasLimit (cechShapeLarge d ≫ F) :=
  hasLimit_iff_restrict_of_leftCofinal _ (cechShapeLarge_isLeftCofinal d hU) F

end SerrePositivity.InfinityCategories.Sheaves
