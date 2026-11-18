module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletion

/-!
模型。文献の定義との比較は後で
# 正規化削除語の非零辺切断の有限添字

概要：Berger–Fresse §1.2.3・§2.2.7 の全削除和に現れる全射かつ非退化な削除語を保持する。
方針：削除位置・削除後非零切断・削除後全射性を一つの有限型にまとめる。
規約：削除後の非退化性は切断の非零性から導く。
使われ方：三種類の削除項を同じ実際のテンソル成分で比較する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：全射な削除語の非零辺切断の添字（BF §1.2.3・§2.2.7）。
方針：削除位置・切断位置と必要な二つの証明を保持する。
規約：非全射削除と退化切断は含まない。
使われ方：正規化全削除和の添字型。 -/
@[ext] structure NormalizedDeletedCut {n l : ℕ} (u : Fin (l + 1) → Fin n) where
  /-- 概要：元の削除位置（BF §1.2.3）。
  方針：元の有限位置を保持する。
  規約：削除後切断点はこの位置を飛ばして戻す。
  使われ方：削除係数。 -/
  deleted : Fin (l + 1)
  /-- 概要：削除後の非零切断点（BF §2.2.7）。
  方針：削除後の有限位置を保持する。
  規約：元位置への像は succAbove。
  使われ方：切断符号と出力族。 -/
  pivot : Fin l
  /-- 概要：削除後の全射性（BF §1.2.3）。
  方針：全ての色の残存を保持する。
  規約：削除語が実際の正規化基底語になる条件。
  使われ方：削除基底語の構成。 -/
  surjective : Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u deleted)
  /-- 概要：削除後の辺切断の非零性（BF §2.2.7）。
  方針：実際の切断非退化性を保持する。
  規約：削除語の隣接非退化性も含意する。
  使われ方：実際の削除出力テンソル。 -/
  nondegenerate : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u deleted) pivot

variable {n l : ℕ} {u : Fin (l + 1) → Fin n}

/-- 概要：正規化削除切断の添字は有限（BF §2.2.7）。
方針：二つの有限位置の組への単射を使う。
規約：証明フィールドは個数を増やさない。
使われ方：全削除和。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.instFiniteNormalizedDeletedCut : Finite (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut u) :=
  Finite.of_injective (fun c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut u => (c.deleted, c.pivot)) (by
    intro c d h
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h)

/-- 概要：有限な正規化削除切断を全て列挙する（BF §2.2.7）。
方針：有限性から Fintype を選ぶ。
規約：非計算的な選択は列挙だけ。
使われ方：実際のテンソル値の有限和。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.instFintypeNormalizedDeletedCut : Fintype (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut u) := Fintype.ofFinite _

namespace NormalizedDeletedCut

/-- 概要：元切断が非零である削除切断の部分型（BF §2.2.7）。
方針：元の切断非退化性で分類する。
規約：障害項を含まない。
使われ方：反復色一因子の境界との比較。 -/
abbrev Regular (u : Fin (l + 1) → Fin n) :=
  {c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut u // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u (c.deleted.succAbove c.pivot)}

/-- 概要：切断点以外の障害を持つ削除切断の部分型（BF §2.2.7）。
方針：元切断の退化性と削除色・切断点色の不一致を要求する。
規約：障害位置の選択はこの型に追加しない。
使われ方：既存の固定点なし対合への有限同値。 -/
abbrev Nonpivot (u : Fin (l + 1) → Fin n) :=
  {c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut u // ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u (c.deleted.succAbove c.pivot) ∧
    u c.deleted ≠ u (c.deleted.succAbove c.pivot)}

/-- 概要：切断点自身が同色障害である削除切断の部分型（BF §2.2.7）。
方針：削除色と元切断点色の一致で分類する。
規約：元切断の退化性は自動的に従う。
使われ方：既存の切断点障害全削除和との有限同値。 -/
abbrev Pivot (u : Fin (l + 1) → Fin n) :=
  {c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut u // u c.deleted = u (c.deleted.succAbove c.pivot)}

/-- 概要：正規化削除切断の実際の削除基底語（BF §1.2.3）。
方針：保持した全射性と非零切断から得る非退化性を付ける。
規約：元次数 d+1 から d へ移る。
使われ方：全削除和を実際の正規化区間テンソルへ送る。 -/
def word {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1)) (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedDeletedCut u.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d :=
  ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u.val c.deleted, c.surjective, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nondegenerate_of_edgeNondegenerate c.nondegenerate⟩

end NormalizedDeletedCut
end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
