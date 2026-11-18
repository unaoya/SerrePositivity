module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeNondegenerate

/-!
模型。文献の定義との比較は後で
# 合成語の実際の非退化全射基底

概要：Berger–Fresse §1.2.4 の正の内側 arity の合成語を基底語として束ねる。
方針：語長・全射性・非退化性を同じ有限語へ移し、正規化との一致を示す。
規約：外側 arity m+1、内側 n>0、出力 arity m+n・次数 d+e。
使われ方：合成保存で各合成項を実際の基底として経路の table と照合する。
-/

@[expose] public section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：各合成語が表す実際の非退化全射基底語（BF §1.2.4）。
方針：正しい長さの有限添字へ実際の合成語の評価を移す。
規約：内側 arity は正。
使われ方：各分割に対応する合成の基底を指定する。 -/
def compositeBasisWord {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e))
    (hn : 0 < n) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + n) (d + e) := by
  let hlen := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_length u v k r
  let f := Fin.cast hlen.symm
  refine ⟨fun i => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r)[(f i).val], ?_, ?_⟩
  · intro a
    obtain ⟨j, hj⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_surjective u v k r a
    exact ⟨Fin.cast hlen j, hj⟩
  · intro i j hij
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_nondegenerate u v k r hn (f i) (f j) hij

/-- 概要：合成の基底語のリスト表示は元の合成語（BF §1.2.4）。
方針：長さと各位置の評価を比較する。
規約：有限添字の移送は値を変えない。
使われ方：正規化生成元と実際の基底の一致を得る。 -/
lemma compositeBasisWord_list {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n) :
    List.ofFn (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn).val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_length]
  · intro i hi hj
    simp only [List.getElem_ofFn, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord, Fin.val_cast]

/-- 概要：正の内側 arity の正規化合成項は実際の基底ベクトル（BF §1.2.4）。
方針：基底語のリスト表示と正規化公式を使う。
規約：任意の可換環、係数は 1。
使われ方：合成保存の有限和の項を非退化基底の項として比較する。 -/
lemma compositeGenerator_eq_basis (A : Type u) [CommRing A] {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hn : 0 < n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeGenerator A u v k r =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A (m + n) (d + e) (ULift.up (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeGenerator
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord_list u v k r hn, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator_ofFn, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_word]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
