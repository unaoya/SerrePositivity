module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.IntervalEndpoints
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# 単体的区間の有限直積の座標面が指定した座標に一致する

## 概要
単体的区間の有限直積の座標面が指定した座標に一致する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0510][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0510
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual finite products of the simplicial interval and their coordinate faces
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube

def obj (n : ℕ) : SSet.{v} where
  obj m := Fin n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval.obj m
  map f := ↾fun x i => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval.map f (x i)
  map_id m := by
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    exact types_congr_hom (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval.map_id m) (x i)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    exact types_congr_hom (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval.map_comp f g) (x i)

def coordinate {n : ℕ} (i : Fin n) : obj n ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval where
  app _ := ↾fun x => x i
  naturality {_ _} _ := by apply ConcreteCategory.hom_ext; intro x; rfl

def endpoint (ε : Bool) (T : SSet.{v}) : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval := if ε then _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one T else _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero T

def face {n : ℕ} (j : Fin (n + 1)) (ε : Bool) : obj n ⟶ obj (n + 1) where
  app m := ↾fun x => Fin.insertNth j ((endpoint ε (obj n)).app m x) x
  naturality {m m'} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    funext k
    induction k using j.succAboveCases with
    | x =>
      change Fin.insertNth (α := fun _ => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval.obj m') j _ _ j =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval.map θ (Fin.insertNth (α := fun _ => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval.obj m) j _ _ j)
      simp only [Fin.insertNth_apply_same]
      convert types_congr_hom ((endpoint ε (obj n)).naturality θ) x using 1 <;> rfl
    | p k =>
      change Fin.insertNth (α := fun _ => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval.obj m') j _ _ (j.succAbove k) =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval.map θ (Fin.insertNth (α := fun _ => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval.obj m) j _ _ (j.succAbove k))
      simp only [Fin.insertNth_apply_succAbove]
      rfl

/-- 単体的区間の有限直積の座標面が指定した座標に一致する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma face_coordinate_same {n : ℕ} (j : Fin (n + 1)) (ε : Bool) :
    face j ε ≫ coordinate j = endpoint ε (obj n) := by
  ext m x
  change Fin.insertNth (α := fun _ => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval.obj m) j _ x j = _
  exact Fin.insertNth_apply_same _ _ _

lemma face_coordinate_other {n : ℕ} (j : Fin (n + 1)) (ε : Bool) (i : Fin n) :
    face j ε ≫ coordinate (j.succAbove i) = coordinate i := by
  ext m x
  change Fin.insertNth (α := fun _ => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval.obj m) j _ x (j.succAbove i) = _
  exact Fin.insertNth_apply_succAbove _ _ _ _

def coordinateOrZero (n k : ℕ) : obj n ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval :=
  if h : k < n then coordinate ⟨k, h⟩ else _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero (obj n)

lemma coordinateOrZero_lt {n k : ℕ} (h : k < n) :
    coordinateOrZero n k = coordinate ⟨k, h⟩ := dite_eq_left h

lemma coordinateOrZero_last (n : ℕ) : coordinateOrZero n n = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero (obj n) :=
  dite_eq_right (Nat.lt_irrefl n)

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube
