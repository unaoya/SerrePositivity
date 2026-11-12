module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.SphereConeData
public import SerrePositivity.KST.NonConnective.DGKappaUnconditionalStageSupply

/-!
概要：K-B3 の切替済み段提供者に、D-S の同じ strict data を代入する。
方針：提供者の cone と D-2 新入力の定義上一致を使う。
規約：data の値は既存の実例そのもの。全単体 map と edgeIso は別工程。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
open CategoryTheory DifferentialGraded KST.NonConnective KST.SConstruction
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ)

/-- 切替後の同じ段提供者の全入力射に対する、固定した D-S strict data。 -/
def dgSuspensionUnconditionalMapData
    {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) :
    DGKappaSuspensionMapData R A B
      (dgKappaUnconditionalStageProvider R κ hκ A).cone
      (dgKappaUnconditionalStageProvider R κ hκ B).cone :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgKappaSphereClosureSuspensionMapData R A B f.down κ hκ

/-- 採用 data の cone は、同じ新閉包代表間の D-3 全 Hom 共役関手。 -/
lemma dgSuspensionUnconditionalMapData_cone
    {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) :
    (dgSuspensionUnconditionalMapData R κ hκ f).cone =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionFunctor R A B f.down hκ Fact.out := rfl

/-- 採用段提供者に対する、同じ実平坦商間の厳密 dg 入力射。 -/
def dgSuspensionUnconditionalInputMap
    {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) :
    dgKappaSuspensionKInput R A (dgKappaUnconditionalStageProvider R κ hκ A).cone ⟶
      dgKappaSuspensionKInput R B (dgKappaUnconditionalStageProvider R κ hκ B).cone :=
  dgKappaSuspensionInputMap R A B _ _ (dgSuspensionUnconditionalMapData R κ hκ f)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
