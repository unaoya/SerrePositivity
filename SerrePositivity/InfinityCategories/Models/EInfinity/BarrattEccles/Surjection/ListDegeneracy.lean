module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ListGenerators
public import Mathlib.Data.List.Chain

/-!
模型。文献の定義との比較は後で
# 隣接重複を持つリストの正規化

概要：Berger–Fresse §1.4.1 の退化な出力が自由加群で零になることを証明する。
方針：語の非退化条件をリストの隣接非一致へ移して矛盾させる。
規約：長さが不一致なら既存の正規化が零を返す。
使われ方：退化な BE 列に対する TR の消滅を項ごとに証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable (A : Type u) [CommRing A]

/-- 概要：隣接非一致を満たさないリストの正規化は零（BF §1.4.1）。
方針：非退化な有限語なら各隣接添字の値が異なることを使う。
規約：任意の長さ・arity で適用する。
使われ方：行の境界の重複から TR の項の消滅を導く。 -/
lemma listGenerator_eq_zero_of_not_isChain {n d : ℕ} (xs : List (Fin n))
    (hxs : ¬ xs.IsChain (· ≠ ·)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator A (d := d) xs = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator
  split
  · rename_i hlen
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_eq_zero_of_not_nondegenerate
    intro hnd
    apply hxs
    apply List.isChain_iff_getElem.mpr
    intro i hi
    exact hnd ⟨i, by omega⟩ ⟨i + 1, by omega⟩ rfl
  · rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
