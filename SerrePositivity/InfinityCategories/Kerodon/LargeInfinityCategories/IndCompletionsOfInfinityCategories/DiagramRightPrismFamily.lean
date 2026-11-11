module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramRightPrismCurry

/-!
概要：元の C 全族と指定 D への全円柱から、元の diagram comma の実族を構成する。
方針：内部 Hom の随伴を戻し、同じ厳密な引き戻しへ写す。
規約：両全境界と C 全族・全円柱を厳密に回収する。
使われ方：点追加の再構成を同じ元の図式 comma に戻す。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) {T : SSet.{u + 1}}
  (P : T ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj C)
  (W : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T (Δ[0] : SSet.{u + 1}) ⊗
    (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
  (hl : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl T (Δ[0] : SSet.{u + 1}) ▷
    (SSet.uliftFunctor.{u + 1, u}).obj K) ≫ W = P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C)
  (hr : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr T (Δ[0] : SSet.{u + 1}) ▷
    (SSet.uliftFunctor.{u + 1, u}).obj K) ≫ W =
    snd (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K) ≫ D)
/-- 概要：元の全族と全円柱を同じ実 comma で保持する。
方針：随伴と引き戻し。規約：全射の等号。使われ方：元の族への帰還。 -/
def diagramRightPrismFamily : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.commaFamilyLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramYoneda κ K C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramRightFamilyCurry P) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramRightPrismCurry κ W)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramRightPrismCurry_old κ P W hl) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramRightPrismCurry_tip κ D W hr)
/-- 概要：元の全族と全円柱を同じ実 comma で保持する。
方針：随伴と引き戻し。規約：全射の等号。使われ方：元の族への帰還。 -/
lemma diagramRightPrismFamily_projection :
    diagramRightPrismFamily κ D P W hl hr ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaProjection κ D =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramRightFamilyCurry P :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.commaFamilyLift_projection _ _ _ _ _ _
/-- 概要：元の全族と全円柱を同じ実 comma で保持する。
方針：随伴と引き戻し。規約：全射の等号。使われ方：元の族への帰還。 -/
lemma diagramRightPrismFamily_originalFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaOriginalFamily κ D (diagramRightPrismFamily κ D P W hl hr) = P := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaOriginalFamily, ← Category.assoc,
    diagramRightPrismFamily_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramRightFamilyCurry, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, uncurry_curry, ← Category.assoc,
    SymmetricCategory.symmetry, Category.id_comp]
/-- 概要：元の全族と全円柱を同じ実 comma で保持する。
方針：随伴と引き戻し。規約：全射の等号。使われ方：元の族への帰還。 -/
lemma diagramRightPrismFamily_prism :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRightPrism κ D (diagramRightPrismFamily κ D P W hl hr) = W := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRightPrism, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaPrism]
  change (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T (Δ[0] : SSet.{u + 1})) _).hom ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ (𝟙 Δ[0]) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (pullback.snd _ _)) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, diagramRightPrismFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.commaFamilyLift_uncurry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramRightPrismCurry, uncurry_curry, ← Category.assoc,
    SymmetricCategory.symmetry, Category.id_comp]
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
