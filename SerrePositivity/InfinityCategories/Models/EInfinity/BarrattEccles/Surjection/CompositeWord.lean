module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Substitution
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OccurrenceOrder
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ListGenerators

/-!
模型。文献の定義との比較は後で
# 分割添字ごとの合成語と正しい次数

概要：Berger–Fresse §1.2.4 の端点を重ねた分割から合成語を構成する。
方針：外側語の全出現へ部分語を代入し、総長の等式を部分長の総和から得る。
規約：外側 arity m+1、内側 n、次数 d と e、出力 arity m+n・次数 d+e。
使われ方：部分合成の正規化生成元を実際の有限和で定義する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：一つの重なる分割に対応する合成語（BF §1.2.4）。
方針：分割部分語を外側語の指定値の各出現へ順に代入する。
規約：nullary の空語の一部分割も同じ定義で扱う。
使われ方：χ の部分合成の各項の語。 -/
def compositeWord {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) :
    List (Fin (m + n)) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (List.ofFn u.val) (r.segments v.val)

/-- 概要：全合成語の長さは出力 arity＋入力次数の和（BF §1.2.4）。
方針：指定値の出現回数を消した元の語長に、全部分語の総長を足す。
規約：空語の挿入も含み、非退化性はまだ主張しない。
使われ方：部分合成の正規化が正しい次数へ写ることを保証する。 -/
lemma compositeWord_length {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r).length = m + n + (d + e) := by
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_length k (List.ofFn u.val) (r.segments v.val)
    (by rw [r.segments_length]; rfl)
  rw [List.length_ofFn, r.segments_flatten_length] at hs
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (List.ofFn u.val) (r.segments v.val)).length = _
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (List.ofFn u.val) (r.segments v.val)).length +
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = (m + 1 + d) + (n + e + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k - 1) at hs
  omega

/-- 概要：合成語を正しい次数の基底元か零へ正規化（BF §1.2.4）。
方針：既存の listGenerator で退化・非全射を零へ送る。
規約：符号は別に付与する。
使われ方：有限和の各合成項の値。 -/
def compositeGenerator (A : Type*) [CommRing A] {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A (m + n) (d + e) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
