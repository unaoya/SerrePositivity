module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLift

/-!
# 二重の単体的宇宙liftを一つのliftへ平坦化する自然同型を構成する

## 概要
二重の単体的宇宙liftを一つのliftへ平坦化する自然同型を構成する。
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
[棚卸し m0597][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0597
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A natural flattening isomorphism for two actual simplicial universe lifts
-/

@[expose] public section
universe v a b
noncomputable section
open CategoryTheory

namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/- 旧宣言の技術注記：
Flatten wrappers without identifying the independent universe parameters.
-/
/-- 二重の単体的宇宙liftを一つのliftへ平坦化する自然同型を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。
-/
def iterationIso : SSet.uliftFunctor.{a, v} ⋙ SSet.uliftFunctor.{b, max a v} ≅
    SSet.uliftFunctor.{max a b, v} :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun x => ULift.up x.down.down
      invFun := fun x => ULift.up (ULift.up x.down)
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }) (by intro n m θ; ext x; rfl))
    (by intro K L f; ext n x; rfl)

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
