module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ConeTensorUniverseBoundaries
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndConeTensorExtension

/-!
概要：持ち上げた元の二形状の実余錐積上で、同じ scalar comma の両全族を延長する。
方針：小さい形状へ比較し、既存の全拡張を同じ宇宙比較の逆で戻す。
規約：旧族と下方族を全射の等号で保持し、追加の充填仮定を課さない。
使われ方：有限半順序形状の点追加で元の二族を同時に補間する。

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
/-- 概要：元の二形状を持ち上げた同じ全積で、両全境界を保つ実拡張が存在。
方針：小さい全拡張を宇宙移送。規約：全射の等号。使われ方：実終点 comma の補間。 -/
lemma exists_indComma_coneTensor_native_extension (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {C A L : SSet.{u}} [Quasicategory C] (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) _⦋0⦌)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ A) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ L)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj A ⊗
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) x)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ⊗
      (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) x)
    (h : ((SSet.uliftFunctor.{u + 1, u}).obj A ◁
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ F =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ▷
        (SSet.uliftFunctor.{u + 1, u}).obj L) ≫ G) :
    ∃ E : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ⊗
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) x,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ▷
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ E = F ∧
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ◁
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ E = G := by
  have hs : (SSet.uliftFunctor.{u + 1, u}).map (A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L (Δ[0] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorOldUniverseShape A L ≫ F) =
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (Δ[0] : SSet.{u}) ▷ L) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorLowerUniverseShape A L ≫ G) := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorOldUniverseShape_boundary, Category.assoc, h,
      ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorLowerUniverseShape_boundary, Category.assoc]
  obtain ⟨E, hF, hG⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_indComma_coneTensor_extension κ x hA hL
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorOldUniverseShape A L ≫ F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorLowerUniverseShape A L ≫ G) hs
  refine ⟨inv (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorUniverseShape A L) ≫ E, ?_, ?_⟩
  · apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorOldUniverseShape A L)).mp
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorUniverseShape_old, Category.assoc,
      IsIso.hom_inv_id_assoc, hF]
  · apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorLowerUniverseShape A L)).mp
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTensorUniverseShape_lower, Category.assoc,
      IsIso.hom_inv_id_assoc, hG]
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
