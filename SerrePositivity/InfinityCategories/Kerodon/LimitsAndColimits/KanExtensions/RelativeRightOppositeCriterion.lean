module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeRightCanonical
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.OppositeHomotopyInvolution

/-!
概要：元の相対右 Kan 条件を反転した元の相対左 Kan 条件として判定する。
方針：標準局所錐の反転判定を二度適用し、二重反転の異種等式で元へ戻す。
規約：右側の定義を反転後の条件で代用しない。
使われ方：元の相対右 Kan 関手の全部分圏と左側の制限の反転同型。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：標準相対右 Kan 条件は元と標的と図式の異種等式で移送できる。
方針：単体集合の等式を消去し、図式の等式で同じ条件へ戻す。
規約：底の射 U も異種等式で同時に移す。
使われ方：二重反転した標準相対右条件を元へ戻す。 -/
lemma kanIsRelativeRightKanExtendedFrom_iff_of_heq_data
    {K K' C C' D D' E E' : SSet.{u}}
    (hK : K = K') (hC : C = C') (hD : D = D') (hE : E = E')
    (δ : K ⟶ C) (δ' : K' ⟶ C') (U : D ⟶ E) (U' : D' ⟶ E')
    (F : C ⟶ D) (F' : C' ⟶ D') (hδ : HEq δ δ') (hU : HEq U U') (hF : HEq F F') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeRightKanExtendedFrom U δ F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeRightKanExtendedFrom U' δ' F' := by
  cases hK
  cases hC
  cases hD
  cases hE
  have hd := eq_of_heq hδ
  have hu := eq_of_heq hU
  have hf := eq_of_heq hF
  subst δ' U' F'
  rfl

/-- 概要：元の標準相対右 Kan 条件は反転した標準相対左 Kan 条件と同値。
方針：左から右への反転判定に二重反転の対象・射の一致を合成する。
規約：D と E のみ quasicategory とし、δ と U の充填性は要求しない。
使われ方：元の相対右 Kan 関手の制限定理を左側へ渡す。 -/
lemma kanIsRelativeRightKanExtendedFrom_iff_op_left {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) (δ : K ⟶ C) (F : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeRightKanExtendedFrom U δ F ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom (SSet.opFunctor.map U) (SSet.opFunctor.map δ)
        (SSet.opFunctor.map F) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtendedFrom_iff_op_right
    (SSet.opFunctor.map U) (SSet.opFunctor.map δ) (SSet.opFunctor.map F)
  have he := kanIsRelativeRightKanExtendedFrom_iff_of_heq_data
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.opposite_opposite_eq K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.opposite_opposite_eq C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.opposite_opposite_eq D) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.opposite_opposite_eq E)
    (SSet.opFunctor.map (SSet.opFunctor.map δ)) δ
    (SSet.opFunctor.map (SSet.opFunctor.map U)) U
    (SSet.opFunctor.map (SSet.opFunctor.map F)) F
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.opposite_map_map_heq δ) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.opposite_map_map_heq U) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.opposite_map_map_heq F)
  exact he.symm.trans h.symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.3.2.18"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeRightKanExtendedFrom_iff_op_left
