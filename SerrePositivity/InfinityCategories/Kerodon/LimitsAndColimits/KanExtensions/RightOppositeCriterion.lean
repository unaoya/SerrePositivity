module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.OppositeHomotopyInvolution
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.TransportOppositeReflection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightCylinder

/-!
概要：指定右 Kan 変換を保持して左 Kan 条件へ双対化する。
方針：左条件の反転による判定に二重反転の異種等式を合成する。
規約：変換の存在だけでなく、元の指定変換そのものを戻す。
使われ方：左 Kan の大域的 Hom 普遍性を右 Kan へ移す。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：右 Kan 条件は対象と図式と指定変換の異種等式で移送できる。
方針：対象の等式を消去し、図式とホモトピーの等式へ帰着する。
規約：変換は raw な円柱射の異種等式で指定する。
使われ方：二重反転した右 Kan 条件の正規化。 -/
lemma kanIsRightKanExtension_iff_of_heq_data
    {K K' C C' D D' : SSet.{u}} (hK : K = K') (hC : C = C') (hD : D = D')
    (δ : K ⟶ C) (δ' : K' ⟶ C') (F₀ : K ⟶ D) (F₀' : K' ⟶ D')
    (F : C ⟶ D) (F' : C' ⟶ D')
    (α : SSet.Homotopy (δ ≫ F) F₀) (α' : SSet.Homotopy (δ' ≫ F') F₀')
    (hδ : HEq δ δ') (h₀ : HEq F₀ F₀') (hF : HEq F F') (hα : HEq α.h α'.h) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ F₀ F α ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ' F₀' F' α' := by
  cases hK
  cases hC
  cases hD
  have hd := eq_of_heq hδ
  have h0 := eq_of_heq h₀
  have hf := eq_of_heq hF
  subst δ'
  subst F₀'
  subst F'
  have ha : α = α' := SSet.RelativeMorphism.Homotopy.ext (eq_of_heq hα)
  subst α'
  rfl

/-- 概要：指定右 Kan 変換の反転は左 Kan 変換である。
方針：左条件の反転判定へ元の右条件を二重反転で移送して渡す。
規約：標的 D のみ quasicategory とする。
使われ方：右 Kan 拡張の Hom 普遍性の双対化。 -/
lemma kanIsRightKanExtension_opposite {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (α : SSet.Homotopy (δ ≫ F) F₀)
    (hα : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ F₀ F α) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension (SSet.opFunctor.map δ) (SSet.opFunctor.map F₀)
      (SSet.opFunctor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanOppositeTransformation δ F₀ F α) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsLeftKanExtension_iff_opposite _ _ _ _).2
  apply (kanIsRightKanExtension_iff_of_heq_data
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.opposite_opposite_eq K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.opposite_opposite_eq C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.opposite_opposite_eq D)
    _ δ _ F₀ _ F _ α (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.opposite_map_map_heq δ) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.opposite_map_map_heq F₀)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.opposite_map_map_heq F) ?_).2 hα
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.homotopyOpposite_double_h_heq α

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
