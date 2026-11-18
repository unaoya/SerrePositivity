module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Sequence

/-!
模型。文献の定義との比較は後で
# 一文字行の削除と挿入による Schedule の対応

概要：Berger–Fresse §1.4.4 の頂点境界の添字を元の一文字行と対応させる。
方針：succAbove で長さ 1 の成分を除き、insertNth で復元する。
規約：行を消すと次数が一つ下がり、arity は変わらない。
使われ方：一文字行の削除和を BE の頂点境界の有限和へ付け替える。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：一文字行を除いた行長は一つ低い次数の Schedule（BF §1.4.4）。
方針：総和を指定成分と残りに分解し、長さ 1 を引く。
規約：指定行以外の長さを succAbove の順に保つ。
使われ方：元の table の一文字行から頂点削除の table を作る。 -/
def scheduleDelete {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1)) (i : Fin (d + 2))
    (hi : (r.val i).val = 1) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d :=
  ⟨fun j => r.val (i.succAbove j), by
    refine ⟨fun j => r.property.1 _, ?_⟩
    change (∑ j, (r.val (i.succAbove j)).val) = n + d
    have hs := r.property.2
    rw [Fin.sum_univ_succAbove _ i, hi] at hs
    omega⟩

/-- 概要：任意の位置に一文字行を挿入した行長（BF §1.4.4）。
方針：insertNth の新しい成分が総和を一つ増やすことを計算する。
規約：arity は正であり、長さ 1 を許す。
使われ方：頂点境界の table の添字から元の一文字行を復元する。 -/
def scheduleInsert {n d : ℕ} (hn : 0 < n) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (i : Fin (d + 2)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1) :=
  ⟨i.insertNth ⟨1, by omega⟩ r.val, by
    constructor
    · intro j
      refine Fin.succAboveCases i ?_ (fun k => ?_) j
      · simp
      · simpa using r.property.1 k
    · rw [Fin.sum_univ_succAbove _ i]
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      rw [r.property.2]
      omega⟩

/-- 概要：挿入位置の行長は 1（BF §1.4.4）。
方針：insertNth の指定成分を評価する。
規約：有限添字の自然数値を比較する。
使われ方：復元した行が一文字行の部分型に属することを確認する。 -/
@[simp] lemma scheduleInsert_at {n d : ℕ} (hn : 0 < n) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (i : Fin (d + 2)) : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleInsert hn r i).val i).val = 1 := by
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleInsert]

/-- 概要：挿入した一文字行を除くと元の Schedule（BF §1.4.4）。
方針：全成分で insertNth と succAbove を簡約する。
規約：Schedule の証明項には依存しない。
使われ方：一文字行の添字対応の一方の逆を示す。 -/
@[simp] lemma scheduleDelete_insert {n d : ℕ} (hn : 0 < n) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (i : Fin (d + 2)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleInsert hn r i) i (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleInsert_at hn r i) = r := by
  apply Subtype.ext
  funext j
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleInsert]

/-- 概要：削除した一文字行を同じ位置へ戻すと元の Schedule（BF §1.4.4）。
方針：挿入位置とそれ以外の全位置に分けて比較する。
規約：指定成分の長さは 1。
使われ方：一文字行の添字対応のもう一方の逆を示す。 -/
lemma scheduleInsert_delete {n d : ℕ} (hn : 0 < n) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1))
    (i : Fin (d + 2)) (hi : (r.val i).val = 1) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleInsert hn (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete r i hi) i = r := by
  apply Subtype.ext
  funext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · apply Fin.ext
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleInsert, Fin.insertNth_apply_same] using hi.symm
  · simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleInsert, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete]

/-- 概要：指定位置が一文字行の Schedule と頂点削除後の Schedule の全単射（BF §1.4.4）。
方針：行の削除と挿入を互いに逆とする。
規約：全ての行位置を含み、最終行も除外しない。
使われ方：退化出力を含む頂点境界の項の添字を正確に付け替える。 -/
def singletonScheduleEquiv {n d : ℕ} (hn : 0 < n) (i : Fin (d + 2)) :
    {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1) // (r.val i).val = 1} ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d where
  toFun r := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete r.val i r.property
  invFun r := ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleInsert hn r i, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleInsert_at hn r i⟩
  left_inv r := Subtype.ext (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleInsert_delete hn r.val i r.property)
  right_inv r := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete_insert hn r i

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
