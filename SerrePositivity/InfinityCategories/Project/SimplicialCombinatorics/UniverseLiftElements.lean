module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers
public import Mathlib.CategoryTheory.Elements

/-!
# 既知の宇宙liftの単体圏と元の単体圏の同値を構成する

## 概要
既知の宇宙liftの単体圏と元の単体圏の同値を構成する。
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
[棚卸し m0592][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0592
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Explicit simplex-category equivalence for a known universe lift

Only the ULift wrapper on each original simplex is changed. All degrees
and simplex operators are preserved. This is not a shrinking construction
for an arbitrary large simplicial set.
-/

@[expose] public section
universe w v
noncomputable section
open CategoryTheory

namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
variable (X : SSet.{v})

def downElements : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} X).Elements ⥤ X.Elements where
  obj e := X.elementsMk e.obj e.val.down
  map f := Functor.Elements.homMk f.hom (congrArg ULift.down f.map_val)

def upElements : X.Elements ⥤ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} X).Elements where
  obj e := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} X).elementsMk e.obj (ULift.up e.val)
  map f := Functor.Elements.homMk f.hom (congrArg ULift.up f.map_val)

/-- 既知の宇宙liftの単体圏と元の単体圏の同値を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。
-/
def elementsEquivalence : X.Elements ≌ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} X).Elements where
  functor := upElements X
  inverse := downElements X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intro _ _ _; rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intro _ _ _; rfl)

lemma downElements_degree (e : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} X).Elements) :
    ((downElements X).obj e).obj = e.obj := rfl

lemma downElements_operator {e e' : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{w} X).Elements} (f : e ⟶ e') :
    ((downElements X).map f).hom = f.hom := rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
