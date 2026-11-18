module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSourceWords
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Composition

/-!
模型。文献の定義との比較は後で
# 元の全成功二表と分割の和を両線形部分合成へ同定

概要：Berger–Fresse §1.5.6–9 の元の側の有限和を二つの TR 和の部分合成へ戻す。
方針：成功基底語と分割の依存直和へ添字変更し、各 onSequence の展開と両線形性を使う。
規約：任意の可換環と正の内側 arity。退化入力列も許す。
使われ方：全 shuffle 側の和と合わせて一般の正の内側 arity の TR 合成保存を得る。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable (A : Type u) [CommRing A]

/-- 概要：元の成功二表と分割の和は二列の成功基底語の compositionOnWords 和（BF §1.5.6）。
方針：固定元データの同値で二列の成功型と分割の依存直和へ移し、全分割和をまとめる。
規約：元データの有限型は既存の成功経路との同値から局所的に選ぶ。
使われ方：元の側の全有限和を部分合成の基底上の公式へ戻す。 -/
lemma sum_source_eq_word_sums {m n d e : ℕ} (hn : 0 < n)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1)) :
    letI := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sourceFintype hn outer inner k
    (∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Source outer inner k, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sourceTerm A c) =
      ∑ u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulWord outer, ∑ v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulWord inner,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords A u.val.2 v.val.2 k := by
  classical
  let _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sourceFintype hn outer inner k
  let f : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.WordSource outer inner k → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A (m + n) (d + e) := fun p =>
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionSign p.1.val.2 p.2.1.val.2 k p.2.2 •
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeGenerator A p.1.val.2 p.2.1.val.2 k p.2.2
  calc
    _ = ∑ p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.WordSource outer inner k, f p := by
      apply Fintype.sum_equiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.wordsEquiv hn outer inner k)
      intro c
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sourceTerm_toWords A c
    _ = _ := by
      simp only [Fintype.sum_sigma, f, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords]

/-- 概要：元の全成功二表と分割の和は二つの onSequence の部分合成（BF §1.5.6）。
方針：各入力の成功基底和を両線形部分合成へ代入し、基底上の分割和の式を使う。
規約：正の内側 arity。入力置換列の非退化性は仮定しない。
使われ方：一般の TR 部分合成保存の元の側の全有限和。 -/
lemma sum_source_eq_partialComposition {m n d e : ℕ} (hn : 0 < n)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1)) :
    letI := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sourceFintype hn outer inner k
    (∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Source outer inner k, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sourceTerm A c) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m n d e k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A outer) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A inner) := by
  classical
  let _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sourceFintype hn outer inner k
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sum_source_eq_word_sums A hn outer inner k]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_eq_sum_successfulWords A (Nat.zero_lt_succ m) outer,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_eq_sum_successfulWords A hn inner]
  simp only [map_sum, LinearMap.sum_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition_basis]
  rw [Finset.sum_comm]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：正の内側 arity の全 shuffle 合成の TR は入力 TR の部分合成（BF §1.5.6–9）。
方針：全経路・全 Schedule の符号付き和を成功二表と分割へ移し、両線形部分合成に戻す。
規約：任意の可換環・全次数・全外側 arity。退化入力と零項も含む。
使われ方：一般の正規化 TR オペラッド射の合成保存の正の内側 arity の場合。 -/
lemma onSequence_partialComposition_of_pos (A : Type u) [CommRing A] {m n d e : ℕ}
    (hn : 0 < n) (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1)) :
    (∑ s : ShufflePath d e, (s.sign : ℤ) • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A (fun j =>
      permutationComposition m n k (outer (s.horizontal j)) (inner (s.vertical j)))) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m n d e k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A outer) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A inner) := by
  let _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sourceFintype hn outer inner k
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sum_onSequence_eq_source A hn outer inner k).trans
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sum_source_eq_partialComposition A hn outer inner k)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
