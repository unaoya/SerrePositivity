module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeWord
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DeletionSigns

/-!
模型。文献の定義との比較は後で
# 部分語の行次数と合成の Koszul 符号

概要：Berger–Fresse §1.2.5 の部分語の交換に伴う符号を定義する。
方針：区間の両端より前の区切り数の差を成分次数とし、後続外側次数との積を足す。
規約：右から順に代入し、内側成分を外側の後続成分の前へ動かす。
使われ方：χ の部分合成の有限和に原典の整数符号を付ける。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：自然数位置の前にある区切りの個数（BF §1.2.5）。
方針：有限語の位置から指定された上界より前の区切りだけを数える。
規約：空語の場合も零で定義できる。
使われ方：空部分語を含む成分の行次数を同じ式で扱う。 -/
def lineRank {n l : ℕ} (v : Fin l → Fin n) (p : ℕ) : ℕ :=
  (Finset.univ.filter (fun j => j.val < p ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v j)).card

/-- 概要：有限位置の lineRank は既存の区切り順位（BF §1.2.2・§1.2.5）。
方針：Fin の順序を自然数値の順序として読む。
規約：位置自身の区切りは数えない。
使われ方：行次数の符号を削除・table reduction の既存順位と接続する。 -/
@[simp] lemma lineRank_fin {n l : ℕ} (v : Fin l → Fin n) (p : Fin l) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank v p := rfl

/-- 概要：位置が進むと行番号は減らない（BF §1.2.5）。
方針：上界の小さい区切り集合を大きいものへ包含する。
規約：上界は語長を超えてもよい。
使われ方：部分語の行次数の差が非負で加法的であることを示す。 -/
lemma lineRank_mono {n l : ℕ} (v : Fin l → Fin n) : Monotone (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v) := by
  intro a b hab
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact ⟨lt_of_lt_of_le hj.1 hab, hj.2⟩

/-- 概要：成分の次数は端点を共有する連結に加法的（BF §1.2.5）。
方針：単調な行番号の差を望ましい二つの差へ分ける。
規約：端点は a≤b≤c。
使われ方：合成符号と shuffle の辺数の一致を証明する基礎。 -/
lemma lineRank_sub_add {n l : ℕ} (v : Fin l → Fin n) (a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v b - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v a) + (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v c - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v b) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v c - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v a := by
  have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_mono v hab
  have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_mono v hbc
  omega

/-- 概要：内側の分割部分語が交わる行の数−1（BF §1.2.5）。
方針：開始位置と終了位置の行番号の差を取る。
規約：空部分語の場合は零。
使われ方：各内側成分が持つ Koszul 次数を指定する。 -/
def segmentDegree {n l t : ℕ} (v : Fin l → Fin n) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l) (j : Fin t) : ℕ :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v (r.start j + (r.val j).val - 1) - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v (r.start j)

/-- 概要：右から順に代入する際の全 Koszul 交換の指数（BF §1.2.5）。
方針：各内側成分次数と、対応する出現より後の外側の総行次数との積を足す。
規約：外側の次数は d、指定出現の行番号を引いて後続成分の次数とする。
使われ方：部分合成の各分割項の符号を決める。 -/
def compositionExponent {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) : ℕ :=
  ∑ j, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree v.val r j * (d - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank u.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k j))

/-- 概要：部分合成の一つの合成語の整数符号（BF §1.2.5）。
方針：Koszul 交換の指数に対して (−1) を累乗する。
規約：係数環の標数は仮定しない。
使われ方：合成語の有限和を任意の可換環の自由加群で評価する。 -/
def compositionSign {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) : ℤ :=
  (-1) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionExponent u v k r

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
