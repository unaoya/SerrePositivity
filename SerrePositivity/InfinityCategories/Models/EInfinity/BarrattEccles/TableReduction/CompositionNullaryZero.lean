module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NullaryCompositionSum
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SequenceDegeneracy

/-!
模型。文献の定義との比較は後で
# 出力零 arity を含む空語挿入の合成保存

概要：Berger–Fresse §0・§1.5.7–9 の nullary 次数零の全 arity の TR 合成保存を閉じる。
方針：出力零では正次数の元の列は退化し、次数零では唯一の置換語と空語を計算する。
規約：全外側 arity と全外側次数、任意の可換環。
使われ方：一般の全 arity の正規化 TR 合成保存。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection _root_.SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 概要：出力 arity 零の指定値削除列でも TR は空語合成を保つ（BF §0・§1.5.7–9）。
方針：外側正次数では隣接置換が一致、次数零では唯一の置換語の削除が空語となる。
規約：外側列の退化性は入力に要求しない。
使われ方：nullary 合成保存で正の出力 arity の残りの境界を閉じる。 -/
lemma onSequence_nullary_composition_zero_output (d : ℕ)
    (w : Fin (d + 1) → Equiv.Perm (Fin 1)) (τ : Equiv.Perm (Fin 0)) (k : Fin 1) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A (fun j => permutationComposition 0 0 k (w j) τ) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A 0 0 d 0 k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A w)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A 0 0 (ULift.up (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord (1 : Equiv.Perm (Fin 0))))) := by
  cases d with
  | zero =>
    have ho : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A w =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A 1 0 (ULift.up (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord (1 : Equiv.Perm (Fin 1)))) := by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_degree_zero A (by decide)]
      calc
        _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord (1 : Equiv.Perm (Fin 1))).val := by
          apply congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A)
          funext i
          exact Subsingleton.elim _ _
        _ = _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_word A _
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_nullary_zero, ho, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition_basis]
    rw [Fin.eq_zero k, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords_nullary_of_count_eq_one A _ _ _ (by decide)]
    rfl
  | succ d =>
    have ho : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A w = 0 :=
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_eq_zero_of_adjacent_eq A w 0 1 (by simp)
        (Subsingleton.elim _ _)
    rw [ho]
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_nullary_succ, map_zero, LinearMap.zero_apply]

/-- 概要：内側空語の全 shuffle 和で TR は全外側 arity の部分合成を保つ（BF §1.5.7–9）。
方針：唯一の零垂直次数の経路を評価し、正の出力と出力零の場合を適用する。
規約：出力 arity 零と全次数を含む。
使われ方：一般の合成保存を全 arity でまとめる。 -/
lemma onSequence_partialComposition_nullary_zero {m d : ℕ} (k : Fin (m + 1))
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin 1 → Equiv.Perm (Fin 0)) :
    (∑ s : ShufflePath d 0, (s.sign : ℤ) • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A (fun j =>
      permutationComposition m 0 k (outer (s.horizontal j)) (inner (s.vertical j)))) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m 0 d 0 k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A outer) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A inner) := by
  by_cases hm : 0 < m
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_partialComposition_nullary_zero_of_pos A hm k outer inner
  · have hm' : m = 0 := by omega
    subst m
    let _ : Unique (ShufflePath d 0) :=
      ⟨⟨zeroRightPath d⟩, fun s => s.rightZero_unique (zeroRightPath d)⟩
    simp only [Fintype.sum_unique, ShufflePath.sign_rightZero, Units.val_one, one_smul,
      ShufflePath.horizontal_rightZero, Fin.eq_zero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_nullary_zero_basis]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_nullary_composition_zero_output A d outer (inner 0) 0

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
