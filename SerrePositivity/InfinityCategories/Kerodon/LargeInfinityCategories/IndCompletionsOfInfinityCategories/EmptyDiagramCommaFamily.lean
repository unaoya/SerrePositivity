module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.EmptyShapeTensor
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramRightPrismRecovery

/-!
概要：元の空形状の diagram comma では、任意の全試験族が一意に存在する。
方針：C 全族と全円柱を始対象から作り、同じ二全成分で一意性を検査する。
規約：C に対象の非空性を課さず、元の全図式 D を保持する。
使われ方：空の有限半順序図式の実余錐と単一 filtered 表示。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) (hK : ¬ K.Nonempty)
/-- 概要：元の空形状の comma への任意の試験族の全写像を構成する。
方針：元の二全成分を始対象から作る。規約：元の D。使われ方：空形状の基底。 -/
def emptyDiagramCommaFamily (T : SSet.{u + 1}) : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramRightPrismFamily κ D
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.emptyShapeTensorIsInitial hK T).to _)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.emptyShapeTensorIsInitial hK (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T (Δ[0] : SSet.{u + 1}))).to _)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.emptyShapeTensorIsInitial hK T).hom_ext _ _)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.emptyShapeTensorIsInitial hK (Δ[0] : SSet.{u + 1})).hom_ext _ _)
include hK
/-- 概要：元の空形状の同じ comma への任意の全族は等しい。
方針：元の C 全族と全円柱の一意性。規約：全射の等号。使われ方：旧族の厳密回収。 -/
lemma emptyDiagramComma_hom_ext {T : SSet.{u + 1}} (q r : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D) : q = r := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma_rightFamily_ext κ D
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.emptyShapeTensorIsInitial hK T).hom_ext _ _
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.emptyShapeTensorIsInitial hK (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T (Δ[0] : SSet.{u + 1}))).hom_ext _ _
/-- 概要：元の空形状の同じ comma の任意の全試験族には実余錐がある。
方針：全余錐写像を作り一意性で旧族を回収。規約：元の q。使われ方：帰納の基底。 -/
lemma nonempty_emptyDiagramComma_cocone {T : SSet.{u + 1}} (q : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) :=
  ⟨⟨emptyDiagramCommaFamily κ D hK (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T (Δ[0] : SSet.{u + 1})),
    emptyDiagramComma_hom_ext κ D hK _ _⟩⟩
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
