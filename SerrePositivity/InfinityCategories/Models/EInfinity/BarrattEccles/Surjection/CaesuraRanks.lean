module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CaesuraGaps
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.RawCaesuraOrder

/-!
模型。文献の定義との比較は後で
# 列挙された区切り位置の順位と削除係数

概要：Berger–Fresse §1.2.3・§1.4.4 の第 i 区切りの削除符号を (−1)^i と同定する。
方針：それより前の区切りを Fin i と一対一に対応させて数える。
規約：区切りの番号は零から数える。
使われ方：table の行番号と削除微分の係数を接続する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：列挙された区切り位置は狭義単調（BF §1.2.2）。
方針：区切りの昇順のリストの評価を使う。
規約：添字は Fin d。
使われ方：前の区切り位置の集合を前の添字で記述する。 -/
lemma caesuraAt_strictMono {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) : StrictMono (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v) := by
  intro i j hij
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList v).get _ < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList v).get _
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList_sortedLT v).strictMono_get
  exact hij

/-- 概要：第 i 区切りの前にある区切りは i 個（BF §1.2.3）。
方針：それより小さい区切りの部分型と Fin i の全単射を構成する。
規約：語は次数 d の基底語。
使われ方：削除係数の指数を区切りの番号へ直す。 -/
lemma caesuraRank_caesuraAt {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (i : Fin d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i) = i.val := by
  have hi : i.val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawCaesuraList v.val).length := by
    change i.val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList v).length
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraList_length]
    exact i.isLt
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank_raw_get v.val ⟨i.val, hi⟩

/-- 概要：第 i 区切りの削除係数は (−1)^i（BF §1.2.3・§1.4.4）。
方針：区切りの係数の式に順位の計算を代入する。
規約：整数係数。
使われ方：一文字行の削除符号を BE 頂点境界の符号と比較する。 -/
lemma deletionCoefficient_caesuraAt {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (i : Fin d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i) = (-1 : ℤ) ^ i.val := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_of_caesura _ _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt_caesura v i), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank_caesuraAt]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
