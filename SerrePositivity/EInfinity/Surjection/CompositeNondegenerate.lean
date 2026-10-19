module

public import SerrePositivity.EInfinity.Surjection.CompositeSurjectivity
public import SerrePositivity.EInfinity.Surjection.SubstitutionNondegenerate
public import SerrePositivity.EInfinity.Surjection.OccurrenceSuffixes

/-!
# 正の内側 arity の合成語の非退化性

概要：Berger–Fresse §1.2.4 の合成語は正の内側 arity で基底語を表すことを証明する。
方針：元の二語の隣接非一致を部分語へ制限し、非空部分語の代入の補題を使う。
規約：空語の挿入は別の分岐として正規化で処理する。
使われ方：TR の合成保存で非退化な合成項と table の経路を照合する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection

/-- 概要：正の内側 arity の全合成語は隣接非一致（BF §1.2.4）。
方針：各分割部分語が非空で隣接非一致であることを確認してリスト代入へ渡す。
規約：内側次数と外側 arity・次数は任意。
使われ方：合成語の正規化で隣接退化による零項が生じないことを示す。 -/
lemma compositeWord_isChain {m n d e : ℕ} (u : BasisWord (m + 1) d) (v : BasisWord n e)
    (k : Fin (m + 1)) (r : OverlapPartition (occurrenceCount u.val k) (n + e))
    (hn : 0 < n) : (compositeWord u v k r).IsChain (· ≠ ·) := by
  apply substitute_isChain k (List.ofFn u.val) (r.segments v.val)
    (isChain_ofFn_of_nondegenerate u.val u.nondegenerate)
    (by rw [r.segments_length]; rfl)
  intro part hpart
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hpart
  constructor
  · intro hempty
    have hl := r.segment_length v.val i
    rw [hempty, List.length_nil] at hl
    have hp := r.positive (by omega) i
    omega
  · exact ((isChain_ofFn_of_nondegenerate v.val v.nondegenerate).drop (r.start i)).take _

/-- 概要：正の内側 arity の合成語の有限位置の評価は非退化（BF §1.2.4）。
方針：リストの隣接非一致を有限添字の条件へ直す。
規約：合成語の実際の長さの有限添字。
使われ方：合成の基底語を構成するための非退化条件。 -/
lemma compositeWord_nondegenerate {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e)) (hn : 0 < n) :
    Nondegenerate (fun j : Fin (compositeWord u v k r).length =>
      (compositeWord u v k r)[j.val]) := by
  intro i j hij
  have hc := List.isChain_iff_getElem.mp (compositeWord_isChain u v k r hn) i.val
    (by have := j.isLt; omega)
  simpa only [hij] using hc

end SerrePositivity.EInfinity.Surjection
