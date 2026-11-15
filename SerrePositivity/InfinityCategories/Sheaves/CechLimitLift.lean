module

public import SerrePositivity.InfinityCategories.Sheaves.CechLimitRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.SpecifiedCofinalLimitLift

/-!
概要：指定 Čech 極限錐から、同じ頂点の元の極限錐と指定した比較同値を回収する。
方針：弱終性から証明した元の cofinality に、指定全錐の回収を適用する。
使われ方：BS Construction 4.18 脚注10、HTT 4.1.3.1、Kerodon §7.2（Tag 02MZ）。
規約：制限の厳密な等号は要求しない。頂点の等号と錐圏での指定同値を保持する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
namespace SerrePositivity.InfinityCategories.Sheaves

/-- 元の Čech 錐への指定比較同値を含む、同じ頂点の全極限錐。
制限の厳密な等号は要求しない。 -/
def cechLimitLift {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
    {U : C} (hU : CategoryTheory.IsWeaklyTerminal U) (d : CategoryTheory.CechNerveData U)
    (F : Presheaf C E) (t : JoinCone (cechShape d ≫ F)) (ht : IsLimitCone t) :
    CofinalLimitLiftData (cechShape d) F t :=
  specifiedCofinalLimitLift _ (cechShape_isLeftCofinal d hU) F t ht

/-- drafts の元の型：Čech 極限錐と同じ頂点を持つ全極限錐が存在する。
指定比較同値は cechLimitLift.comparison に保持する。制限の厳密な等号は要求しない。 -/
theorem exists_limitCone_of_cech {C : Type u} [SmallCategory C]
    {E : SSet.{u + 1}} [Quasicategory E] {U : C}
    (hU : CategoryTheory.IsWeaklyTerminal U) (d : CategoryTheory.CechNerveData U)
    (F : Presheaf C E) (t : JoinCone (cechShape d ≫ F)) (ht : IsLimitCone t) :
    ∃ c : JoinCone F, IsLimitCone c ∧ c.vertex = t.vertex :=
  let a := cechLimitLift hU d F t ht
  ⟨a.cone, a.isLimit, a.vertex_eq⟩

/-- 大きい site でも同じ小さい Čech 錐への指定比較同値を保持する。
制限の厳密な等号は要求しない。 -/
def cechLimitLiftLarge {C : Type (u + 1)} [Category.{u} C]
    {E : SSet.{u + 1}} [Quasicategory E] {U : C}
    (hU : CategoryTheory.IsWeaklyTerminal U) (d : CategoryTheory.CechNerveData U)
    (F : nerve Cᵒᵖ ⟶ E) (t : JoinCone (cechShapeLarge d ≫ F)) (ht : IsLimitCone t) :
    CofinalLimitLiftData (cechShapeLarge d) F t :=
  specifiedCofinalLimitLift _ (cechShapeLarge_isLeftCofinal d hU) F t ht

/-- 大きい site の drafts の元の型。指定比較は cechLimitLiftLarge.comparison。
制限の厳密な等号は要求しない。 -/
theorem exists_limitCone_of_cech_large {C : Type (u + 1)} [Category.{u} C]
    {E : SSet.{u + 1}} [Quasicategory E] {U : C}
    (hU : CategoryTheory.IsWeaklyTerminal U) (d : CategoryTheory.CechNerveData U)
    (F : nerve Cᵒᵖ ⟶ E) (t : JoinCone (cechShapeLarge d ≫ F)) (ht : IsLimitCone t) :
    ∃ c : JoinCone F, IsLimitCone c ∧ c.vertex = t.vertex :=
  let a := cechLimitLiftLarge hU d F t ht
  ⟨a.cone, a.isLimit, a.vertex_eq⟩

end SerrePositivity.InfinityCategories.Sheaves
