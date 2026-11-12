module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TensorShapePushout
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramRightPrismFamily

/-!
概要：元の形状 pushout で貼った C 全族と全円柱は、同じ両全境界を保つ。
方針：左直積の pushout の一意性と、積の二因子の交換則を使う。
規約：元の全族と指定 D 側面を全射の等号で保持する。
使われ方：貼り合わせた元の diagram comma 族の構成。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {J K₁ K₂ K : SSet.{u}} {i : J ⟶ K₁} {j : J ⟶ K₂}
  {r : K₁ ⟶ K} {s : K₂ ⟶ K} (h : IsPushout i j r s)
  {T X Y : SSet.{u + 1}} (y : X ⟶ Y)
  (P₁ : T ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K₁ ⟶ X)
  (P₂ : T ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K₂ ⟶ X)
  (W₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T (Δ[0] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K₁ ⟶ Y)
  (W₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T (Δ[0] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K₂ ⟶ Y)
  (hP : (T ◁ (SSet.uliftFunctor.{u + 1, u}).map i) ≫ P₁ =
    (T ◁ (SSet.uliftFunctor.{u + 1, u}).map j) ≫ P₂)
  (hW : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T (Δ[0] : SSet.{u + 1}) ◁ (SSet.uliftFunctor.{u + 1, u}).map i) ≫ W₁ =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T (Δ[0] : SSet.{u + 1}) ◁ (SSet.uliftFunctor.{u + 1, u}).map j) ≫ W₂)
/-- 概要：貼った全円柱の旧族境界は貼った同じ C 全族の像。
方針：元の積 pushout で検査。規約：全射の等号。使われ方：元の comma 族への帰還。 -/
lemma tensorShapeGlue_prism_old
    (h₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl T (Δ[0] : SSet.{u + 1}) ▷
      (SSet.uliftFunctor.{u + 1, u}).obj K₁) ≫ W₁ = P₁ ≫ y)
    (h₂ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl T (Δ[0] : SSet.{u + 1}) ▷
      (SSet.uliftFunctor.{u + 1, u}).obj K₂) ≫ W₂ = P₂ ≫ y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl T (Δ[0] : SSet.{u + 1}) ▷ (SSet.uliftFunctor.{u + 1, u}).obj K) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.tensorShapeGlue h W₁ W₂ hW = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.tensorShapeGlue h P₁ P₂ hP ≫ y := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.tensorShape_isPushout h T).hom_ext
  · rw [← Category.assoc, whisker_exchange, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.tensorShapeGlue_left, h₁,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.tensorShapeGlue_left]
  · rw [← Category.assoc, whisker_exchange, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.tensorShapeGlue_right, h₂,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.tensorShapeGlue_right]
/-- 概要：貼った全円柱の指定 D 側面は元の D 自身。
方針：元の積 pushout で検査。規約：全射の等号。使われ方：元の全図式の保持。 -/
lemma tensorShapeGlue_prism_tip (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ Y)
    (h₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr T (Δ[0] : SSet.{u + 1}) ▷
      (SSet.uliftFunctor.{u + 1, u}).obj K₁) ≫ W₁ =
      snd (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K₁) ≫
        (SSet.uliftFunctor.{u + 1, u}).map r ≫ D)
    (h₂ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr T (Δ[0] : SSet.{u + 1}) ▷
      (SSet.uliftFunctor.{u + 1, u}).obj K₂) ≫ W₂ =
      snd (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K₂) ≫
        (SSet.uliftFunctor.{u + 1, u}).map s ≫ D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr T (Δ[0] : SSet.{u + 1}) ▷ (SSet.uliftFunctor.{u + 1, u}).obj K) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.tensorShapeGlue h W₁ W₂ hW =
      snd (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K) ≫ D := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.tensorShape_isPushout h (Δ[0] : SSet.{u + 1})).hom_ext
  · rw [← Category.assoc, whisker_exchange, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.tensorShapeGlue_left, h₁]
    simp only [← Category.assoc, whiskerLeft_snd]
  · rw [← Category.assoc, whisker_exchange, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.tensorShapeGlue_right, h₂]
    simp only [← Category.assoc, whiskerLeft_snd]
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
