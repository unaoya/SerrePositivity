module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Fintype.Card

/-!
模型。文献の定義との比較は後で
# Surjection オペラッドの非退化な全射語

概要：Berger–Fresse §1.2.1 の基底を、隣接値が異なる有限全射語で表す。
方針：語の長さと arity を独立に持ち、次数 d の基底では長さ n+d に特殊化する。
規約：値と位置を Fin で零から数え、空語も含める。
使われ方：χ の自由加群・削除微分・table reduction の出力の添字となる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：有限語の隣接値が常に異なるという非退化条件（BF §1.2.1）。
方針：位置の差が 1 である任意の二つの添字を比較する。
規約：空語と一文字の語では条件は空。
使われ方：退化な語を自由加群の零元へ送る。 -/
def Nondegenerate {n l : ℕ} (u : Fin l → Fin n) : Prop :=
  ∀ i j : Fin l, i.val + 1 = j.val → u i ≠ u j

/-- 概要：非退化条件は有限計算で判定できる（BF §1.2.1）。
方針：有限個の位置の組を全て調べる。
規約：選択公理による非計算的な判定を使わない。
使われ方：任意の語を基底か零へ正規化する。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.instDecidableNondegenerate {n l : ℕ} (u : Fin l → Fin n) : Decidable (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate u) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate
  infer_instance

/-- 概要：単射な語は非退化（BF §1.2.1）。
方針：隣接位置の値の一致から位置の一致を導いて矛盾する。
規約：全射性は要求しない。
使われ方：次数零の置換を基底語にする。 -/
lemma nondegenerate_of_injective {n l : ℕ} {u : Fin l → Fin n}
    (hu : Function.Injective u) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate u := by
  intro i j hij h
  have hval := congrArg Fin.val (hu h)
  omega

/-- 概要：長さ l、arity n の非退化な全射語（BF §1.2.1）。
方針：全射性と隣接値の非一致を持つ関数の部分型を取る。
規約：長さを次数から独立に扱う。
使われ方：削除と table の行の組合せを同じ型の族で扱う。 -/
abbrev Word (n l : ℕ) :=
  {u : Fin l → Fin n // Function.Surjective u ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate u}

/-- 概要：χ(n) の鎖次数 d の基底となる語（BF §1.2.1）。
方針：全射語の長さを n+d に固定する。
規約：d 鎖は後で整数コチェイン次数 −d に置く。
使われ方：surjection オペラッドの次数成分の自由基底を与える。 -/
abbrev BasisWord (n d : ℕ) := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n (n + d)

namespace Word

/-- 概要：全射語の各値には出現位置がある（BF §1.2.1）。
方針：部分型の全射性を取り出す。
規約：出現位置の選択をデータとして固定しない。
使われ方：最後の出現と区切り位置を構成する。 -/
lemma surjective {n l : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) : Function.Surjective u.val := u.property.1

/-- 概要：基底語には同じ値が隣接しない（BF §1.2.1）。
方針：部分型の非退化条件を取り出す。
規約：添字は自然数の差で比較する。
使われ方：削除後の退化条件と表の境界を検証する。 -/
lemma nondegenerate {n l : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate u.val := u.property.2

/-- 概要：全射語の arity は長さ以下（BF §1.2.1）。
方針：有限集合の全射に対する濃度の不等式を使う。
規約：零 arity・空語も含む。
使われ方：次数を語の長さと arity の差で計算する。 -/
lemma arity_le_length {n l : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) : n ≤ l := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective u.val u.surjective

end Word

/-- 概要：arity 0 の正次数には語が存在しない（BF §1.2.1）。
方針：最初の文字が空の値集合に属するという矛盾を使う。
規約：arity 0・次数 0 の空語は排除しない。
使われ方：零入力演算の次数成分を扱う。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.instIsEmptyBasisWordOfNatNatHAdd (d : ℕ) : IsEmpty (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 (d + 1)) :=
  ⟨fun u => Fin.elim0 (u.val 0)⟩

/-- 概要：arity 1 の正次数には非退化語が存在しない（BF §1.2.1）。
方針：最初の二つの文字が単元集合の値を持つことを使う。
規約：次数 0 の単位語は排除しない。
使われ方：オペラッドの単位と正次数の退化を計算する。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.instIsEmptyBasisWordOfNatNatHAdd_1 (d : ℕ) : IsEmpty (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 1 (d + 1)) := by
  refine ⟨fun u => ?_⟩
  exact u.nondegenerate 0 ⟨1, by omega⟩ rfl (Subsingleton.elim _ _)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
