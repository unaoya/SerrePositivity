module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftParameterHom

/-!
# 実際の宇宙比較が内部Homの評価と整合する

## 概要
実際の宇宙比較が内部Homの評価と整合する。
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
[棚卸し m0591][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0591
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual universe comparison commutes with currying whole small families
-/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.UniverseLiftClosedCurry

lemma nativeEquiv_symm_curry {K P T : SSet.{v}} (f : K ⊗ T ⟶ P)
    (n : SimplexCategory) (t : T.obj (Opposite.op n)) :
    (SimplexParameterHom.nativeEquiv K P n).symm ((curry f).app (Opposite.op n) t) =
      K ◁ SSet.yonedaEquiv.symm t ≫ f := by
  apply (SimplexParameterHom.nativeEquiv K P n).injective
  rw [Equiv.apply_symm_apply]
  change (curry f).app (Opposite.op n) t =
    SSet.yonedaEquiv (curry (K ◁ SSet.yonedaEquiv.symm t ≫ f))
  rw [curry_natural_left]
  rw [SSet.yonedaEquiv_symm_comp, Equiv.apply_symm_apply]

lemma curry_tensorMap {K P T : SSet.{v}} (f : K ⊗ T ⟶ P) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} (curry f) ≫ (UniverseLiftParameterHom.closedIso K P).hom =
      curry (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.tensorMap.{w} f) := by
  ext n x
  change SimplexParameterHom.nativeEquiv (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P) n.unop
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap ((SimplexParameterHom.nativeEquiv K P n.unop).symm
      ((curry f).app n x.down))) = (curry (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.tensorMap.{w} f)).app n x
  rw [nativeEquiv_symm_curry]
  apply (SimplexParameterHom.nativeEquiv (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P) n.unop).symm.injective
  rw [Equiv.symm_apply_apply, nativeEquiv_symm_curry]
  ext m y
  rfl

lemma curry_lowerTensor {K P T : SSet.{v}}
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K ⊗ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} P) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} (curry (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerTensor f)) ≫
        (UniverseLiftParameterHom.closedIso K P).hom = curry f := by
  rw [curry_tensorMap, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.tensorMap_lowerTensor]

/-- 実際の宇宙比較が内部Homの評価と整合する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。
-/
lemma evaluation (K P : SSet.{v}) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} K ◁ (UniverseLiftParameterHom.closedIso K P).hom ≫
      (ihom.ev (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj K)).app (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj P) =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.tensorMap.{w} ((ihom.ev K).app P) := by
  have h := curry_tensorMap.{w} ((ihom.ev K).app P)
  rw [← uncurry_id_eq_ev, curry_uncurry] at h
  have hi : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} (𝟙 ((ihom K).obj P)) =
      𝟙 (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} ((ihom K).obj P)) := rfl
  rw [hi, Category.id_comp] at h
  have hh := congrArg uncurry h
  rw [uncurry_curry, uncurry_eq] at hh
  exact hh

end SerrePositivity.SimplicialModel.UniverseLiftClosedCurry
