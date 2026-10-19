module

public import SerrePositivity.EInfinity.TableReduction.SingletonTerms
public import SerrePositivity.EInfinity.TableReduction.BoundaryExpressions

/-!
# 一文字行の添字の付け替えと頂点境界の有限和

概要：Berger–Fresse §1.4.4 の一文字行の寄与を頂点境界の和へ付け替える。
方針：一文字行の Schedule と一つ低い次数の Schedule の全単射を使う。
規約：arity は正で、最終頂点も含む。
使われ方：一般の削除対の相殺後に残る有限和を onSequence と同定する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.TableReduction

/-- 概要：指定した一文字行を除く項の和は頂点削除後の TR（BF §1.4.4）。
方針：Schedule の削除・挿入の全単射で有限和を移す。
規約：行抽出に失敗する項も term の定義で零となる。
使われ方：各頂点に対応する削除和を table reduction の値に直す。 -/
lemma sum_singletonSchedules (A : Type u) [CommRing A] {n d : ℕ} (hn : 0 < n)
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) (i : Fin (d + 2)) :
    (∑ r : {r : Schedule n (d + 1) // (r.val i).val = 1},
      term A (fun j => w (i.succAbove j)) (scheduleDelete r.val i r.property)) =
      onSequence A (fun j => w (i.succAbove j)) := by
  rw [onSequence, ite_eq_right (by omega)]
  exact (singletonScheduleEquiv hn i).sum_comp
    (fun r => term A (fun j => w (i.succAbove j)) r)

/-- 概要：一文字行の交代符号を含む有限和は頂点境界の一項（BF §1.4.4）。
方針：行番号にだけ依存する符号を和の外へ出す。
規約：係数環は任意の可換環。
使われ方：全頂点の交代和へ各行の寄与を組み立てる。 -/
lemma sum_signed_singletonSchedules (A : Type u) [CommRing A] {n d : ℕ} (hn : 0 < n)
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) (i : Fin (d + 2)) :
    (∑ r : {r : Schedule n (d + 1) // (r.val i).val = 1},
      (-1 : ℤ) ^ i.val • term A (fun j => w (i.succAbove j))
        (scheduleDelete r.val i r.property)) =
      (-1 : ℤ) ^ i.val • onSequence A (fun j => w (i.succAbove j)) := by
  rw [← Finset.smul_sum, sum_singletonSchedules A hn w i]

/-- 概要：全ての一文字行を頂点ごとに集めた交代和は BE の頂点境界（BF §1.4.4）。
方針：各頂点の Schedule の有限和の公式を足し合わせる。
規約：正の arity、全次数、任意の可換環を扱う。
使われ方：残りの削除対の相殺を示した後、境界恒等式を閉じる。 -/
lemma sum_singletonSchedules_vertexBoundary (A : Type u) [CommRing A] {n d : ℕ}
    (hn : 0 < n) (w : Fin (d + 2) → Equiv.Perm (Fin n)) :
    (∑ i : Fin (d + 2), ∑ r : {r : Schedule n (d + 1) // (r.val i).val = 1},
      (-1 : ℤ) ^ i.val • term A (fun j => w (i.succAbove j))
        (scheduleDelete r.val i r.property)) = vertexBoundary A w := by
  unfold vertexBoundary
  apply Finset.sum_congr rfl
  intro i _
  exact sum_signed_singletonSchedules A hn w i

end SerrePositivity.EInfinity.TableReduction
