module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotDeletionGaps

/-!
模型。文献の定義との比較は後で
# 切断点障害削除項の有限添字

概要：Berger–Fresse §2.2.7 の切断点同色削除を証明付きの有限型として保持する。
方針：削除位置と削除後切断位置を取り、元切断点との同色条件を記録する。
規約：削除位置と元切断点は異なり、左右の二部分へ分かれる。
使われ方：切断点障害の全有限和と隙間への添字替え。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open scoped _root_.BigOperators

/-- 概要：切断点自身を同色障害に持つ非零削除切断（BF §2.2.7）。
方針：削除と残る切断点の同色・非零性を保持する。
規約：元の辺切断は自動的に退化する。
使われ方：切断点障害の削除和の有限添字。 -/
@[ext] structure PivotResidualCut {n l : ℕ} (u : Fin (l + 1) → Fin n) where
  /-- 概要：元の削除位置（BF §2.2.7）。
  方針：元の有限語の位置を保持する。
  規約：残る切断点とは異なる。
  使われ方：削除係数の添字。 -/
  deleted : Fin (l + 1)
  /-- 概要：削除後の切断位置（BF §2.2.7）。
  方針：削除後の有限語の位置を保持する。
  規約：元位置へは succAbove で戻す。
  使われ方：削除後の切断値。 -/
  pivot : Fin l
  /-- 概要：削除後の辺切断の非零性（BF §2.2.7）。
  方針：実際の左右単射性を保持する。
  規約：元切断の非零性は仮定しない。
  使われ方：実際の削除基底語とテンソル値。 -/
  nondegenerate : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u deleted) pivot
  /-- 概要：削除色と元切断点色の一致（BF §2.2.7）。
  方針：切断点自身が同色障害である条件を保持する。
  規約：色の等式は削除位置から切断点への向き。
  使われ方：隙間の側の同色削除として分類する。 -/
  same_color : u deleted = u (deleted.succAbove pivot)

variable {n l : ℕ} {u : Fin (l + 1) → Fin n}

/-- 概要：切断点障害削除の添字型は有限（BF §2.2.7）。
方針：二つの有限位置の組へ単射で写す。
規約：証明のフィールドは個数を増やさない。
使われ方：全削除和の添字。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.instFinitePivotResidualCut : Finite (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut u) :=
  Finite.of_injective (fun c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut u => (c.deleted, c.pivot)) (by
    intro c d h
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h)

/-- 概要：切断点障害削除の有限な全体を列挙する（BF §2.2.7）。
方針：有限性から Fintype を選ぶ。
規約：非計算的な選択は添字の列挙だけ。
使われ方：切断点障害の有限和。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.instFintypePivotResidualCut : Fintype (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut u) := Fintype.ofFinite _

namespace PivotResidualCut

/-- 概要：切断点障害がある元の辺切断は退化（BF §2.2.7）。
方針：非零なら切断点色の唯一性により削除位置も切断点となり矛盾する。
規約：削除後の辺切断は非零。
使われ方：元の非零切断に由来する削除項との分離。 -/
lemma original_degenerate (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut u) :
    ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u (c.deleted.succAbove c.pivot) := by
  intro h
  exact Fin.ne_succAbove c.deleted c.pivot (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivot_unique h c.deleted c.same_color)

/-- 概要：元切断点より左を削除する添字部分（BF §2.2.7）。
方針：位置の厳密順序で部分型を取る。
規約：対応する隙間は元切断点の直前。
使われ方：共通係数が負となる削除和。 -/
abbrev Before (u : Fin (l + 1) → Fin n) :=
  {c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut u // c.deleted < c.deleted.succAbove c.pivot}

/-- 概要：元切断点より右を削除する添字部分（BF §2.2.7）。
方針：逆向きの厳密順序で部分型を取る。
規約：対応する隙間は元切断点の直後。
使われ方：共通係数が正となる削除和。 -/
abbrev After (u : Fin (l + 1) → Fin n) :=
  {c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut u // c.deleted.succAbove c.pivot < c.deleted}

/-- 概要：切断点障害の任意の有限和は左右の二部分の和（BF §2.2.7）。
方針：左右の順序が排反かつ全体を覆うことを使う。
規約：値は任意の可換加法モノイドでよい。
使われ方：実際の削除テンソル和の左右への分割。 -/
lemma sum_split {M : Type*} [AddCommMonoid M] (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut u → M) :
    ∑ c, v c = (∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.Before u, v c.val) + ∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.After u, v c.val := by
  classical
  let e : {c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut u // ¬ c.deleted < c.deleted.succAbove c.pivot} ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.After u :=
    Equiv.subtypeEquivRight (fun c => by
      constructor
      · intro h
        exact lt_of_le_of_ne (le_of_not_gt h) (Fin.succAbove_ne c.deleted c.pivot)
      · exact fun h => not_lt_of_gt h)
  have he : (∑ c : {c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut u // ¬ c.deleted < c.deleted.succAbove c.pivot},
      v c.val) = ∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut.After u, v c.val :=
    Fintype.sum_equiv e _ _ (fun c => by
      change v c.val = v c.val
      rfl)
  rw [← he]
  exact (Fintype.sum_subtype_add_sum_subtype
    (fun c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualCut u => c.deleted < c.deleted.succAbove c.pivot) v).symm

end PivotResidualCut
end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
