module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ListErasure
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.RawListDifferential

/-!
模型。文献の定義との比較は後で
# リスト出力の位置ごとの削除項

概要：Berger–Fresse §1.4.4 の削除微分を実際の出力位置の有限和にする。
方針：リストの eraseIdx に削除係数を掛け、有限語の削除和と比較する。
規約：全射性・非退化性を仮定しない。
使われ方：table の一文字行と残りの削除位置を分割する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable (A : Type u) [CommRing A]

/-- 概要：リスト出力の一位置の符号付き削除項（BF §1.4.4）。
方針：その位置の削除係数と削除リストの正規化を掛ける。
規約：次数は削除後の次数を指定する。
使われ方：削除和を位置の部分集合に分けて比較する。 -/
def listDeletionTerm {n d : ℕ} (xs : List (Fin n)) (k : Fin xs.length) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (fun j : Fin xs.length => xs[j.val]) k •
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator A (xs.eraseIdx k.val)

/-- 概要：同じ長さの有限添字の移送は削除係数を保つ（BF §1.2.3）。
方針：長さの等式について帰納する。
規約：語と削除位置を同じ同値で移す。
使われ方：リスト化で生じる長さの証明項を取り除く。 -/
lemma deletionCoefficient_finCongr {n l m : ℕ} (h : l = m)
    (v : Fin l → Fin n) (k : Fin l) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (v ∘ (finCongr h).symm) ((finCongr h) k) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v k := by
  subst m
  rfl

/-- 概要：有限語の削除項をリスト化しても値は同じ（BF §1.4.4）。
方針：削除語のリスト化と eraseIdx を比較し、生成元の公式を適用する。
規約：有限添字は同じ自然数値のままリストの長さへ移す。
使われ方：有限語の削除和をリスト位置の和へ移す。 -/
lemma listDeletionTerm_ofFn {n d : ℕ} (v : Fin (n + (d + 1)) → Fin n)
    (k : Fin (n + (d + 1))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listDeletionTerm A (d := d) (List.ofFn v)
        ⟨k.val, by simpa only [List.length_ofFn] using k.isLt⟩ =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v k • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v k) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listDeletionTerm
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ofFn_succAbove_eraseIdx v k
  rw [← he]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator_ofFn]
  congr 1
  simp only [List.getElem_ofFn]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_finCongr (List.length_ofFn (f := v)).symm v k

/-- 概要：有限語の削除和はリスト化後の全位置の削除項の和（BF §1.4.4）。
方針：長さの等式による有限添字の同値で和を付け替える。
規約：退化・非全射な語も扱う。
使われ方：実際の出力長を添字とした有限和を導く。 -/
lemma sum_listDeletionTerm_ofFn {n d : ℕ} (v : Fin (n + (d + 1)) → Fin n) :
    (∑ k : Fin (List.ofFn v).length, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listDeletionTerm A (d := d) (List.ofFn v) k) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawDifferential A v := by
  let e : Fin (n + (d + 1)) ≃ Fin (List.ofFn v).length :=
    finCongr (List.length_ofFn (f := v)).symm
  rw [← e.sum_comp]
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawDifferential
  apply Finset.sum_congr rfl
  intro k _
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listDeletionTerm_ofFn A v k

/-- 概要：正しい長さのリストの微分は全ての出力位置の削除項の和（BF §1.4.4）。
方針：出力リストを有限語として読み直し、リスト化の和の公式を戻す。
規約：全射性・非退化性の仮定を追加しない。
使われ方：一文字行の位置と残りの位置への分割を実際の削除微分に適用する。 -/
lemma rawListDifferential_eq_sum {n d : ℕ} (xs : List (Fin n))
    (h : xs.length = n + (d + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawListDifferential A (d := d) xs =
      ∑ k : Fin xs.length, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listDeletionTerm A (d := d) xs k := by
  let v : Fin (n + (d + 1)) → Fin n := fun i => xs[i.val]'(by omega)
  have he : List.ofFn v = xs := by
    apply List.ext_getElem (by simp only [List.length_ofFn]; omega)
    intro i hi hi'
    simp only [List.getElem_ofFn, v]
  have hd : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawListDifferential A (d := d) xs = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawDifferential A v := by
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawListDifferential
    rw [dite_eq_left h]
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawDifferential A v := hd
    _ = ∑ k : Fin (List.ofFn v).length, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listDeletionTerm A (d := d) (List.ofFn v) k :=
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.sum_listDeletionTerm_ofFn A v).symm
    _ = _ := congrArg (fun ys : List (Fin n) =>
      ∑ k : Fin ys.length, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listDeletionTerm A (d := d) ys k) he

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
