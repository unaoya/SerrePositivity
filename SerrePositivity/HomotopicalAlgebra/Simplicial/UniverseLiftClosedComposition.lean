module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftClosedCurry
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ClosedParameterComposition

/-!
# 実際の宇宙比較が内部Homの標準合成を保つ

## 概要
実際の宇宙比較が内部Homの標準合成を保つ。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0590][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0590
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual universe comparison preserves standard closed composition and identity
-/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.UniverseLiftClosedComposition

/-- 実際の宇宙比較が内部Homの標準合成を保つ。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。
-/
lemma composition (K P Q : SSet.{v}) :
    ((UniverseLiftParameterHom.closedIso K P).hom ⊗ₘ
      (UniverseLiftParameterHom.closedIso P Q).hom) ≫
        MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj P) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj Q) =
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.tensorIso.{w} ((ihom K).obj P) ((ihom P).obj Q)).inv ≫
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map (MonoidalClosed.comp K P Q) ≫
        (UniverseLiftParameterHom.closedIso K Q).hom := by
  rw [MonoidalClosed.comp_eq K P Q, UniverseLiftClosedCurry.curry_tensorMap]
  apply uncurry_injective
  rw [uncurry_natural_left, MonoidalClosed.comp_eq, uncurry_curry,
    uncurry_natural_left, uncurry_curry, MonoidalClosed.compTranspose_eq]
  ext n x
  have hf := types_congr_hom (congr_app (UniverseLiftClosedCurry.evaluation.{w} K P) n)
    (x.1, x.2.1)
  have hg := types_congr_hom (congr_app (UniverseLiftClosedCurry.evaluation.{w} P Q) n)
    (ULift.up (((ihom.ev K).app P).app n (x.1.down, x.2.1.down)), x.2.2)
  change ((ihom.ev (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K)).app (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj P)).app n
    (x.1, (UniverseLiftParameterHom.closedIso K P).hom.app n x.2.1) =
      ULift.up (((ihom.ev K).app P).app n (x.1.down, x.2.1.down)) at hf
  change ((ihom.ev (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P)).app (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj Q)).app n
    (ULift.up (((ihom.ev K).app P).app n (x.1.down, x.2.1.down)),
      (UniverseLiftParameterHom.closedIso P Q).hom.app n x.2.2) =
      ULift.up (((ihom.ev P).app Q).app n
        (((ihom.ev K).app P).app n (x.1.down, x.2.1.down), x.2.2.down)) at hg
  change ((ihom.ev (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P)).app (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj Q)).app n
    (((ihom.ev (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj K)).app (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj P)).app n
      (x.1, (UniverseLiftParameterHom.closedIso K P).hom.app n x.2.1),
        (UniverseLiftParameterHom.closedIso P Q).hom.app n x.2.2) = _
  rw [hf]
  exact hg

lemma identity (K : SSet.{v}) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} (MonoidalClosed.id K) ≫ (UniverseLiftParameterHom.closedIso K K).hom =
      toUnit (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (𝟙_ SSet.{v})) ≫ MonoidalClosed.id (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K) := by
  rw [MonoidalClosed.id_eq, UniverseLiftClosedCurry.curry_tensorMap]
  have h : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.tensorMap.{w} (ρ_ K).hom =
      fst (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (𝟙_ SSet.{v})) := by
    ext n x
    rfl
  rw [h, ClosedParameterComposition.curry_fst]

def liftedComposition (K P Q : SSet.{v}) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} ((ihom K).obj P) ⊗ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} ((ihom P).obj Q) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} ((ihom K).obj Q) :=
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.tensorIso.{w} ((ihom K).obj P) ((ihom P).obj Q)).inv ≫
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map (MonoidalClosed.comp K P Q)

lemma inverse_composition (K P Q : SSet.{v}) :
    ((UniverseLiftParameterHom.closedIso K P).inv ⊗ₘ
      (UniverseLiftParameterHom.closedIso P Q).inv) ≫ liftedComposition.{w} K P Q =
    MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj P) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj Q) ≫
      (UniverseLiftParameterHom.closedIso K Q).inv := by
  apply (cancel_mono (UniverseLiftParameterHom.closedIso K Q).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [liftedComposition, Category.assoc, ← composition]
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  simp

def unitParameter (T : SSet.{max w v}) : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} (𝟙_ SSet.{v}) where
  app _ := ↾fun _ => ULift.up PUnit.unit
  naturality _ := by
    intro _ _
    rfl

def unitFrom (K : SSet.{v}) (T : SSet.{max w v}) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} ((ihom K).obj K) :=
  unitParameter T ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map (MonoidalClosed.id K)

lemma unitFrom_eq (K : SSet.{v}) (T : SSet.{max w v}) :
    unitFrom K T = toUnit T ≫ MonoidalClosed.id (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K) ≫
      (UniverseLiftParameterHom.closedIso K K).inv := by
  apply (cancel_mono (UniverseLiftParameterHom.closedIso K K).hom).mp
  simp only [unitFrom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [identity, ← Category.assoc, comp_toUnit]

end SerrePositivity.SimplicialModel.UniverseLiftClosedComposition
