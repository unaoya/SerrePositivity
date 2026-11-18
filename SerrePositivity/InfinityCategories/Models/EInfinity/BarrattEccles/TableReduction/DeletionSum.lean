module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionBijection
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.BoundaryRemainderIdentity

/-!
模型。文献の定義との比較は後で
# 成功削除点上の残余和の分割

概要：Berger–Fresse §1.4.4 の残余削除全体を相殺する二種類に分ける。
方針：孤立した値の零係数を処理し、残る区切り・最終出現を有限部分型で足す。
規約：語の正規化は削除項の評価時に行う。
使われ方：残余削除の全単射を全体の和へ適用する。
-/

@[expose] public section

noncomputable section

universe u


namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：成功削除点の正規化削除項（BF §1.4.4）。
方針：出力の指定位置の既存 listDeletionTerm を評価する。
規約：元の次数 d+1 に対し削除後の次数は d。
使われ方：全成功削除点の有限和の被加数。 -/
def deletionValue (A : Type u) [CommRing A] {n d : ℕ}
    {w : Fin (d + 2) → Equiv.Perm (Fin n)} (p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint w) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listDeletionTerm A p.output p.position

/-- 概要：一文字行を除いた成功削除点の寄与（BF §1.4.4）。
方針：一文字行に属する項は零として残余項だけを保持する。
規約：有限和の添字は全ての成功削除点。
使われ方：元の remainderTerm の和との照合に使う。 -/
def remainingValue (A : Type u) [CommRing A] {n d : ℕ}
    {w : Fin (d + 2) → Equiv.Perm (Fin n)} (p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint w) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d := by
  classical
  exact if p.Remaining then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionValue A p else 0

open _root_.Classical in
/-- 概要：残余の一項は区切り・先行出現を持つ最終出現の二分岐（BF §1.4.4）。
方針：残余で孤立した出現の係数は零であることを使う。
規約：退化した元の出力もその削除項を評価する。
使われ方：残余の全有限和を二つの部分型の和へ分ける。 -/
lemma remainingValue_split (A : Type u) [CommRing A] {n d : ℕ}
    {w : Fin (d + 2) → Equiv.Perm (Fin n)} (p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint w) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainingValue A p =
      (if p.IsFinal then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionValue A p else 0) +
        (if p.IsCaesura then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionValue A p else 0) := by
  classical
  by_cases hr : p.Remaining
  · by_cases hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (fun j : Fin p.output.length => p.output[j.val]) p.position
    · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainingValue, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint.IsFinal, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint.IsCaesura, hr, hc,
        not_true_eq_false, false_and, and_false, and_self, ↓reduceIte, zero_add]
    · by_cases hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences (fun j : Fin p.output.length => p.output[j.val])
          p.position).Nonempty
      · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainingValue, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint.IsFinal, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint.IsCaesura, hr, hc, hp,
          not_false_eq_true, and_self, and_false, ↓reduceIte, add_zero]
      · have hv : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionValue A p = 0 := by
          simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionValue, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listDeletionTerm, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient, ite_eq_right hc,
            dite_eq_right hp, zero_zsmul]
        simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainingValue, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint.IsFinal, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint.IsCaesura, hr, hc, hp,
          not_false_eq_true, and_false, ↓reduceIte, hv, add_zero]
  · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainingValue, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint.IsFinal, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint.IsCaesura, hr, false_and,
      ↓reduceIte, add_zero]

open _root_.Classical in
/-- 概要：成功削除点上の残余和は二種類の削除の和（BF §1.4.4）。
方針：一項の分割を加算し、条件付きの和を有限部分型の和へ移す。
規約：全 Schedule と全出力位置を含む。
使われ方：区切り・最終出現の全単射で残余全体を相殺する。 -/
lemma sum_remainingValue_split (A : Type u) [CommRing A] {n d : ℕ}
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) :
    (∑ p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint w, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainingValue A p) =
      (∑ p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FinalDeletion w, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionValue A p.val) +
        ∑ q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CaesuraDeletion w, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionValue A q.val := by
  classical
  simp_rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainingValue_split]
  rw [Finset.sum_add_distrib]
  congr 1
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_dite_zero_eq_subtype _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint.IsFinal (fun p _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionValue A p)
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_dite_zero_eq_subtype _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint.IsCaesura (fun p _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionValue A p)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
