module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ReversedDegeneracies

/-!
# 向きを反転した単体パラメータの面と退化の対応する恒等式を証明する

## 概要
向きを反転した単体パラメータの面と退化の対応する恒等式を証明する。
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
[棚卸し m0550][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0550
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Reversed parameter faces and their mixed degeneracy identities

All four identities are images of the usual simplex identities under rev
and the standard-simplex functor. No model structure is used.
-/

@[expose] public section
universe r
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

def functor : SimplexCategory ⥤ SSet.{r} := SimplexCategory.rev ⋙ SSet.stdSimplex

def delta (n : ℕ) (i : Fin (n + 2)) :
    SSet.stdSimplex.{r}.obj (SimplexCategory.mk n) ⟶
      SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) := functor.map (SimplexCategory.δ i)

lemma delta_eq (n : ℕ) (i : Fin (n + 2)) : delta n i = SSet.stdSimplex.δ i.rev := by
  simp only [delta, functor, CategoryTheory.Functor.comp_map, SimplexCategory.rev_map_δ]
  rfl

lemma sigma_eq (n : ℕ) (i : Fin (n + 1)) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n i = functor.map (SimplexCategory.σ i) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma, functor, CategoryTheory.Functor.comp_map, SimplexCategory.rev_map_σ]

/-- 向きを反転した単体パラメータの面と退化の対応する恒等式を証明する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma delta_sigma_self (n : ℕ) (i : Fin (n + 1)) :
    delta n i.castSucc ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n i = 𝟙 _ := by
  rw [delta, sigma_eq, ← CategoryTheory.Functor.map_comp,
    SimplexCategory.δ_comp_σ_self, CategoryTheory.Functor.map_id]
  rfl

lemma delta_sigma_succ (n : ℕ) (i : Fin (n + 1)) :
    delta n i.succ ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n i = 𝟙 _ := by
  rw [delta, sigma_eq, ← CategoryTheory.Functor.map_comp,
    SimplexCategory.δ_comp_σ_succ, CategoryTheory.Functor.map_id]
  rfl

lemma delta_sigma_le (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i ≤ j.castSucc) :
    delta (n + 1) i.castSucc ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma (n + 1) j.succ = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n j ≫ delta n i := by
  rw [delta, delta, sigma_eq, sigma_eq, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, SimplexCategory.δ_comp_σ_of_le h]

lemma delta_sigma_gt (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i) :
    delta (n + 1) i.succ ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma (n + 1) j.castSucc = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n j ≫ delta n i := by
  rw [delta, delta, sigma_eq, sigma_eq, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, SimplexCategory.δ_comp_σ_of_gt h]

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
