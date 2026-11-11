module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLift
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
# 実際の連結成分と単体的宇宙liftとの交換を表す全単射を構成する

## 概要
実際の連結成分と単体的宇宙liftとの交換を表す全単射を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間のπ₀、局所化後の射、ホモトピー類の計算に利用できる。
[棚卸し m0601][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0601
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual components commute with the explicit universe lift

The equivalence is defined on vertices and edges, with no model structure.
-/

@[expose] public section
universe v w
noncomputable section
open CategoryTheory

namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
variable {X Y : SSet.{v}}

def up (X : SSet.{v}) : SSet.π₀ X → SSet.π₀ (SSet.uliftFunctor.{w, v}.obj X) :=
  SSet.π₀.lift (fun x => SSet.π₀.mk ⟨x⟩) (fun {_x _y} e => SSet.π₀.sound
    (SSet.Edge.ofTruncated
      { edge := ⟨e.edge⟩
        src_eq := ULift.ext e.src_eq
        tgt_eq := ULift.ext e.tgt_eq }))

def down (X : SSet.{v}) : SSet.π₀ (SSet.uliftFunctor.{w, v}.obj X) → SSet.π₀ X :=
  SSet.π₀.lift (fun x => SSet.π₀.mk x.down) (fun {_x _y} e => SSet.π₀.sound
    (SSet.Edge.ofTruncated
      { edge := e.edge.down
        src_eq := congrArg ULift.down e.src_eq
        tgt_eq := congrArg ULift.down e.tgt_eq }))

/-- 実際の連結成分と単体的宇宙liftとの交換を表す全単射を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
各次数のULiftの上げ下げを明示し、単体作用素との交換を確認する。
写像・充填またはホモトピーを同じ全パラメータのまま移送する。
-/
def equiv (X : SSet.{v}) : SSet.π₀ (SSet.uliftFunctor.{w, v}.obj X) ≃ SSet.π₀ X where
  toFun := down X
  invFun := up X
  left_inv z := by
    obtain ⟨⟨x⟩, rfl⟩ := SSet.π₀.mk_surjective z
    rfl
  right_inv z := by
    obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective z
    rfl

lemma up_naturality (f : X ⟶ Y) (z : SSet.π₀ X) :
    SSet.mapπ₀ (SSet.uliftFunctor.{w, v}.map f) (up X z) = up Y (SSet.mapπ₀ f z) := by
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective z
  rfl

lemma down_naturality (f : X ⟶ Y)
    (z : SSet.π₀ (SSet.uliftFunctor.{w, v}.obj X)) :
    down Y (SSet.mapπ₀ (SSet.uliftFunctor.{w, v}.map f) z) = SSet.mapπ₀ f (down X z) := by
  obtain ⟨⟨x⟩, rfl⟩ := SSet.π₀.mk_surjective z
  rfl

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
