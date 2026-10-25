module

public import SerrePositivity.InfinityCategories.F2.Ind.TensorShapePushout
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramRightPrismFamily

/-!
概要：元の形状 pushout で貼った C 全族と全円柱は、同じ両全境界を保つ。
方針：左直積の pushout の一意性と、積の二因子の交換則を使う。
規約：元の全族と指定 D 側面を全射の等号で保持する。
使われ方：貼り合わせた元の diagram comma 族の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {J K₁ K₂ K : SSet.{u}} {i : J ⟶ K₁} {j : J ⟶ K₂}
  {r : K₁ ⟶ K} {s : K₂ ⟶ K} (h : IsPushout i j r s)
  {T X Y : SSet.{u + 1}} (y : X ⟶ Y)
  (P₁ : T ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K₁ ⟶ X)
  (P₂ : T ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K₂ ⟶ X)
  (W₁ : join T (Δ[0] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K₁ ⟶ Y)
  (W₂ : join T (Δ[0] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj K₂ ⟶ Y)
  (hP : (T ◁ (SSet.uliftFunctor.{u + 1, u}).map i) ≫ P₁ =
    (T ◁ (SSet.uliftFunctor.{u + 1, u}).map j) ≫ P₂)
  (hW : (join T (Δ[0] : SSet.{u + 1}) ◁ (SSet.uliftFunctor.{u + 1, u}).map i) ≫ W₁ =
    (join T (Δ[0] : SSet.{u + 1}) ◁ (SSet.uliftFunctor.{u + 1, u}).map j) ≫ W₂)
/-- 概要：貼った全円柱の旧族境界は貼った同じ C 全族の像。
方針：元の積 pushout で検査。規約：全射の等号。使われ方：元の comma 族への帰還。 -/
lemma tensorShapeGlue_prism_old
    (h₁ : (joinInl T (Δ[0] : SSet.{u + 1}) ▷
      (SSet.uliftFunctor.{u + 1, u}).obj K₁) ≫ W₁ = P₁ ≫ y)
    (h₂ : (joinInl T (Δ[0] : SSet.{u + 1}) ▷
      (SSet.uliftFunctor.{u + 1, u}).obj K₂) ≫ W₂ = P₂ ≫ y) :
    (joinInl T (Δ[0] : SSet.{u + 1}) ▷ (SSet.uliftFunctor.{u + 1, u}).obj K) ≫
      tensorShapeGlue h W₁ W₂ hW = tensorShapeGlue h P₁ P₂ hP ≫ y := by
  apply (tensorShape_isPushout h T).hom_ext
  · rw [← Category.assoc, whisker_exchange, Category.assoc, tensorShapeGlue_left, h₁,
      ← Category.assoc, tensorShapeGlue_left]
  · rw [← Category.assoc, whisker_exchange, Category.assoc, tensorShapeGlue_right, h₂,
      ← Category.assoc, tensorShapeGlue_right]
/-- 概要：貼った全円柱の指定 D 側面は元の D 自身。
方針：元の積 pushout で検査。規約：全射の等号。使われ方：元の全図式の保持。 -/
lemma tensorShapeGlue_prism_tip (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ Y)
    (h₁ : (joinInr T (Δ[0] : SSet.{u + 1}) ▷
      (SSet.uliftFunctor.{u + 1, u}).obj K₁) ≫ W₁ =
      snd (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K₁) ≫
        (SSet.uliftFunctor.{u + 1, u}).map r ≫ D)
    (h₂ : (joinInr T (Δ[0] : SSet.{u + 1}) ▷
      (SSet.uliftFunctor.{u + 1, u}).obj K₂) ≫ W₂ =
      snd (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K₂) ≫
        (SSet.uliftFunctor.{u + 1, u}).map s ≫ D) :
    (joinInr T (Δ[0] : SSet.{u + 1}) ▷ (SSet.uliftFunctor.{u + 1, u}).obj K) ≫
      tensorShapeGlue h W₁ W₂ hW =
      snd (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K) ≫ D := by
  apply (tensorShape_isPushout h (Δ[0] : SSet.{u + 1})).hom_ext
  · rw [← Category.assoc, whisker_exchange, Category.assoc, tensorShapeGlue_left, h₁]
    simp only [← Category.assoc, whiskerLeft_snd]
  · rw [← Category.assoc, whisker_exchange, Category.assoc, tensorShapeGlue_right, h₂]
    simp only [← Category.assoc, whiskerLeft_snd]
end SerrePositivity.InfinityCategories.F2.Ind
