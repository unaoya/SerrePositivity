module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.RightConeTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.F1BNerveComparisonLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Hom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightConstantFamily

/-!
概要：指定余単位を伴う右 Kan 条件を通常の pointwise 条件と比較する。
方針：元の指定局所錐の比較から全頂点の条件を移す。
規約：大域的な Hom 普遍性だけによる Kan 拡張とは区別する。
使われ方：B5 の右 pointwise Kan の古典比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

variable {K C D : Type u} [Category.{u} K] [Category.{u} C] [Category.{u} D]
  (L : K ⥤ C) {F₀ : K ⥤ D} {F : C ⥤ D} (α : L ⋙ F ⟶ F₀)

/-- 概要：指定余単位の native な局所錐の極限性と通常の局所錐の極限性は同値。
方針：局所錐の厳密な比較、添字同型、極限性と代表の不変性を合成する。
規約：元の指定余単位と拡張関手を保持する。
使われ方：B5 の古典 pointwise 右 Kan の双方向回収。 -/
lemma nerveRightConeTransport_isLimit_iff (c : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightConeTransport L α c).cone ↔
    Nonempty (IsLimit ((Functor.RightExtension.mk F α).coneAt c)) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (nerveMap L) (nerveMap F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)
  let j := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeIso c L).hom
  let d := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p j).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightConeTransport L α c).cone
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict_isIso p j
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightConeTransport L α c).cone ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d :=
    ⟨fun h ↦ h.map_of_isIso _, fun h ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_of_trivialKanFibration _ h⟩
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone ((Functor.RightExtension.mk F α).coneAt c)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsLimitCone_congr (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeIso_hom_diagram c L F₀) d _
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightConeTransport_cone L α c)
  exact ha.trans (hb.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone_isLimit_iff _))

/-- 概要：指定余単位の native な右 Kan 条件と通常の pointwise 右 Kan 条件は同値。
方針：局所錐の厳密な比較、添字同型、極限性と代表の不変性を合成する。
規約：元の指定余単位と拡張関手を保持する。
使われ方：B5 の古典 pointwise 右 Kan の双方向回収。 -/
lemma nerve_isRightKanExtensionHom_iff_pointwise :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtensionHom (nerveMap L) (nerveMap F₀) (nerveMap F)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (F := L ⋙ F) (G := F₀) α) ↔
        Nonempty (Functor.RightExtension.mk F α).IsPointwiseRightKanExtension := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isRightKanExtensionHom_iff_of_representative (nerveMap L) (nerveMap F₀) (nerveMap F)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (F := L ⋙ F) (G := F₀) α) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy α)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy_hom α)]
  constructor
  · intro h
    have hc : ∀ c, Nonempty (IsLimit ((Functor.RightExtension.mk F α).coneAt c)) := by
      intro c
      obtain ⟨t, ht⟩ := h (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)
      exact (nerveRightConeTransport_isLimit_iff L α c).1 ((t.isLimitCone_iff
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightConeTransport L α c)).1 ht)
    exact ⟨fun c ↦ Classical.choice (hc c)⟩
  · rintro ⟨h⟩ v
    obtain ⟨c, rfl⟩ := (nerveEquiv (C := C)).symm.surjective v
    exact ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightConeTransport L α c, (nerveRightConeTransport_isLimit_iff L α c).2 ⟨h c⟩⟩

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
