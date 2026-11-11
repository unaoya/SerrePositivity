module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramCommaDiagramTransport

/-!
概要：両局所 comma 族の共有境界での一致を、同じ C 全族と全円柱の一致へ移す。
方針：形状制限の自然性と元の図式等号の表示移送を合成する。
規約：元の全写像と指定境界を等号で保持する。
使われ方：元の余錐を shape pushout の貼り合わせへ渡す。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C] {J K₁ K₂ : SSet.{u}}
  (D₁ : (SSet.uliftFunctor.{u + 1, u}).obj K₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
  (D₂ : (SSet.uliftFunctor.{u + 1, u}).obj K₂ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
  (i : J ⟶ K₁) (j : J ⟶ K₂)
  (hD : (SSet.uliftFunctor.{u + 1, u}).map i ≫ D₁ =
    (SSet.uliftFunctor.{u + 1, u}).map j ≫ D₂)
  {T : SSet.{u + 1}} (q₁ : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D₁) (q₂ : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D₂)
  (hq : (q₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D₁ i) ≫
    eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ) hD) = q₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D₂ j)
include hq
/-- 概要：元の共有境界の局所 comma 族の一致は C 全族の一致を与える。
方針：元の表示移送と制限。規約：全射の等号。使われ方：元の C 全族の貼り合わせ。 -/
lemma diagramCommaGluing_originalFamily_compatible :
    (T ◁ (SSet.uliftFunctor.{u + 1, u}).map i) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaOriginalFamily κ D₁ q₁ =
    (T ◁ (SSet.uliftFunctor.{u + 1, u}).map j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaOriginalFamily κ D₂ q₂ := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaOriginalFamily_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaOriginalFamily_restrict,
    ← hq, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaOriginalFamily_transport κ hD]
/-- 概要：元の共有境界の局所 comma 族の一致は全円柱の一致を与える。
方針：元の表示移送と制限。規約：全射の等号。使われ方：元の全変換の貼り合わせ。 -/
lemma diagramCommaGluing_prism_compatible :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T (Δ[0] : SSet.{u + 1}) ◁ (SSet.uliftFunctor.{u + 1, u}).map i) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRightPrism κ D₁ q₁ =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T (Δ[0] : SSet.{u + 1}) ◁ (SSet.uliftFunctor.{u + 1, u}).map j) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRightPrism κ D₂ q₂ := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRightPrism_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRightPrism_restrict,
    ← hq, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRightPrism_transport κ hD]
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
