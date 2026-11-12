module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftTensor
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# 指定された全区間ホモトピーをモデル構造なしで宇宙liftへ移す

## 概要
指定された全区間ホモトピーをモデル構造なしで宇宙liftへ移す。
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
[棚卸し m0595][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0595
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Lift the same whole simplicial homotopy without a model structure
-/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
variable {K P : SSet.{v}} {f g : K ⟶ P}

/- 旧宣言の技術注記：
The actual lifted interval family, retaining both endpoint maps.
-/
/-- 指定された全区間ホモトピーをモデル構造なしで宇宙liftへ移す。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。
-/
def homotopy (H : SSet.Homotopy f g) : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} f) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{w} g) where
  h := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexTensorMap.{w} H.h
  h₀ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up (congrArg (fun k => k.app n x.down) H.h₀)
  h₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up (congrArg (fun k => k.app n x.down) H.h₁)
  rel := by
    apply NatTrans.ext
    funext n
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
