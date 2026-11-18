module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionPath
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ComponentSuffixSums

/-!
模型。文献の定義との比較は後で
# 合成項の候補経路は元の合成符号を持つ

概要：Berger–Fresse §1.5.6 の候補経路の shuffle 符号と合成語の Koszul 符号を同定する。
方針：成分経路の交換指数を各内側成分×後続外側次数の和に移す。
規約：零次数と内側の空語も含む。
使われ方：候補経路の table reduction を合成語へ照合するときの符号条件を供給する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：候補経路の成分交換指数は元の合成の指数（BF §1.5.6）。
方針：成分列の後続和を自然数区間の和へ移し、外側後続次数の公式を使う。
規約：全 arity・次数で分割が存在する場合に成立する。
使われ方：経路と合成語の二つの符号を比較する。 -/
lemma compositionPath_blockExponent {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockExponent (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionDegreePairs u v k r) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionExponent u v k r := by
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockExponent (List.ofFn (fun i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) =>
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree v.val r i, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerSegmentDegree u.val k (i.val + 1)))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockExponent_ofFn]
  simp only [List.map_drop, List.map_ofFn]
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionExponent
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change ((List.ofFn (fun j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) =>
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerSegmentDegree u.val k (j.val + 1))).drop i.val).sum = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.sum_drop_ofFn_nat (fun j => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerSegmentDegree u.val k (j + 1))]
  exact (Finset.sum_Ico_add' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerSegmentDegree u.val k) i.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 1).trans
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.sum_outerSegmentDegree_suffix u k i)

/-- 概要：候補経路の実際の shuffle 符号は元の合成語の符号（BF §1.5.6）。
方針：成分経路の符号の式に指数の一致を代入し、整数係数へ移す。
規約：任意の可換環へ整数係数として移せる。
使われ方：TR の部分合成保存で有限和の項の符号を一致させる。 -/
lemma compositionPath_sign {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath u v k r).sign : ℤ) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionSign u v k r := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath_sign_blocks, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath_blockExponent]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionSign, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
