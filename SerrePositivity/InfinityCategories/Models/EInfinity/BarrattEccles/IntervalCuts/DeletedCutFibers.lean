module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCuts
public import Mathlib.Data.Fintype.BigOperators

/-!
模型。文献の定義との比較は後で
# 正規化削除切断の削除位置ごとの有限ファイバー

概要：Berger–Fresse §1.2.3 の外側の削除和と §2.2.7 の内側の切断和を共通添字へ移す。
方針：全射な削除位置とその非零切断の依存組を共通有限添字と同一視する。
規約：非全射な削除位置は外側の部分型から除く。
使われ方：実際の削除微分を正規化全削除和へ接続する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open scoped _root_.BigOperators

variable {n l : ℕ} (u : Fin (l + 1) → Fin n)

/-- 概要：共通削除切断添字と全射削除位置・非零切断の依存組との有限同値（BF §2.2.7）。
方針：保持した二位置と二証明を依存組へ並べ替える。
規約：順逆とも実際の削除・切断位置を保つ。
使われ方：削除位置ごとの切断和を一つの全和へまとめる。 -/
def fiberEquiv : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut u ≃
    (Σ i : {i : Fin (l + 1) // Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i)},
      {q : Fin l // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i.val) q}) where
  toFun c := ⟨⟨c.deleted, c.surjective⟩, ⟨c.pivot, c.nondegenerate⟩⟩
  invFun c := ⟨c.1.val, c.2.val, c.1.property, c.2.property⟩
  left_inv _ := rfl
  right_inv c := by rcases c with ⟨⟨i, hi⟩, ⟨q, hq⟩⟩; rfl

/-- 概要：正規化削除切断の全和は全射削除位置ごとの非零切断和（BF §2.2.7）。
方針：依存組との有限同値と依存組上の和公式を使う。
規約：値は任意の可換加法モノイドでよい。
使われ方：実際の削除微分の辺成分を共通全和へ移す。 -/
lemma sum_fibers {M : Type*} [AddCommMonoid M] (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut u → M) :
    ∑ c, v c =
      ∑ i : {i : Fin (l + 1) // Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i)},
        ∑ q : {q : Fin l // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i.val) q},
          v ⟨i.val, q.val, i.property, q.property⟩ := by
  classical
  calc
    _ = ∑ c, v ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.fiberEquiv u).symm c) :=
      Fintype.sum_equiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.fiberEquiv u) _ _ (fun _ => rfl)
    _ = _ := by rw [Fintype.sum_sigma]; rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut
