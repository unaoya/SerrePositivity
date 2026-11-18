module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DeletionSigns
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Sort

/-!
模型。文献の定義との比較は後で
# 任意の有限語の区切りの列と削除順位

概要：Berger–Fresse §1.4.4 の退化した table 出力にも区切り順位の符号を適用する。
方針：全射性や非退化性を使わず、有限位置の昇順の列から順位を数える。
規約：区切りの個数は語に依存し、次数とは同定しない。
使われ方：退化出力を含む全ての table の行末の削除係数を計算する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：任意の有限語の区切り位置の昇順の列（BF §1.2.2）。
方針：全位置の列から後で再出現する位置を切り出す。
規約：基底語であることを要求しない。
使われ方：全ての table 出力の区切り順位を列の添字で扱う。 -/
def rawCaesuraList {n l : ℕ} (v : Fin l → Fin n) : List (Fin l) :=
  (List.finRange l).filter (fun i => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v i)

/-- 概要：区切りの生の列の所属条件（BF §1.2.2）。
方針：有限位置の列の filter を評価する。
規約：位置は Fin l。
使われ方：順位の前にある区切りの部分型を列の添字へ戻す。 -/
@[simp] lemma mem_rawCaesuraList {n l : ℕ} (v : Fin l → Fin n) (i : Fin l) :
    i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawCaesuraList v ↔ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v i := by simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawCaesuraList]

/-- 概要：任意の語の区切り列は狭義単調（BF §1.2.2）。
方針：昇順の全位置の部分列である。
規約：語の値の大小とは無関係。
使われ方：区切りの順位を有限の前の添字で数える。 -/
lemma rawCaesuraList_sortedLT {n l : ℕ} (v : Fin l → Fin n) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawCaesuraList v).SortedLT := by
  rw [List.sortedLT_iff_pairwise]
  exact (List.sortedLT_finRange l).pairwise.filter _

/-- 概要：任意の語の第 i 区切りより前の区切りは i 個（BF §1.2.3）。
方針：前の添字から前の区切り位置への評価を全単射にする。
規約：全射性・非退化性を仮定しない。
使われ方：退化 table の行末でも交代符号を得る。 -/
lemma caesuraRank_raw_get {n l : ℕ} (v : Fin l → Fin n)
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawCaesuraList v).length) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank v ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawCaesuraList v).get i) = i.val := by
  let f : Fin i.val →
      {k : Fin l // k < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawCaesuraList v).get i ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v k} :=
    fun j => ⟨(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawCaesuraList v).get ⟨j.val, by omega⟩,
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawCaesuraList_sortedLT v).strictMono_get (by change j.val < i.val; exact j.isLt),
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.mem_rawCaesuraList v _).mp (List.get_mem _ _)⟩
  have hinj : Function.Injective f := by
    intro a b he
    have hget := congrArg Subtype.val he
    have hab := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawCaesuraList_sortedLT v).strictMono_get.injective hget
    apply Fin.ext
    exact congrArg (fun k : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawCaesuraList v).length => k.val) hab
  have hsurj : Function.Surjective f := by
    intro k
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.mem_rawCaesuraList v k.val).mpr k.property.2)
    have hjlt : j.val < i.val := by
      apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawCaesuraList_sortedLT v).strictMono_get.lt_iff_lt.mp
      rw [hj]
      exact k.property.1
    refine ⟨⟨j.val, hjlt⟩, ?_⟩
    apply Subtype.ext
    exact hj
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  simpa only [Fintype.card_fin, Fintype.card_subtype, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank] using hc.symm

/-- 概要：任意の語の第 i 区切りの削除係数は (−1)^i（BF §1.2.3・§1.4.4）。
方針：区切りの係数の式に前の区切りの個数を代入する。
規約：退化語も含む。
使われ方：全ての成功した table の行番号から削除符号を得る。 -/
lemma deletionCoefficient_raw_get {n l : ℕ} (v : Fin l → Fin n)
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawCaesuraList v).length) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawCaesuraList v).get i) = (-1 : ℤ) ^ i.val := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_of_caesura _ _
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.mem_rawCaesuraList v _).mp (List.get_mem _ _)), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank_raw_get]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
