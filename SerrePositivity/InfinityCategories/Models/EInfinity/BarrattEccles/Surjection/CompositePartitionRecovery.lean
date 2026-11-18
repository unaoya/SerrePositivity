module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.InsertedWordRuns
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeInnerRecovery

/-!
模型。文献の定義との比較は後で
# 合成語から元の全分割部分語と分割を復元する

概要：Berger–Fresse §1.5.9 の分割の一意性を実際の合成語に対して証明する。
方針：元の外側語をたどり、指定値で最大の挿入連続区間を消費する。
規約：元の外側語は非退化。空の内側部分語も同じ復元で扱う。
使われ方：元の両語の一意性と合わせて合成項の元データを一意に決める。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

/-- 概要：外側語と合成語から指定値ごとの全挿入部分語を取り出す（BF §1.5.9）。
方針：指定値では最大挿入区間を、他の値では合成語の先頭一文字を消費する。
規約：外側語の長さで再帰し、区間が空でも停止する。
使われ方：元の分割成分列の計算可能な逆写像。 -/
def splitParts {m n : ℕ} (k : Fin (m + 1)) :
    List (Fin (m + 1)) → List (Fin (m + n)) → List (List (Fin n))
  | [], _ => []
  | a :: xs, out =>
    if a = k then
      ((out.takeWhile (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.isInserted k)).filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) ::
        splitParts k xs (out.dropWhile (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.isInserted k))
    else splitParts k xs out.tail

/-- 概要：非退化な外側語への代入から元の全挿入部分語を復元（BF §1.5.9）。
方針：外側語で帰納し、指定値直後の外側文字で連続区間を止める。
規約：部分語数は出現回数に一致。部分語の非空性は要求しない。
使われ方：実際の分割部分語列の一意性。 -/
lemma splitParts_substitute {m n : ℕ} (k : Fin (m + 1))
    (xs : List (Fin (m + 1))) (parts : List (List (Fin n)))
    (hc : parts.length = xs.count k) (hx : xs.IsChain (· ≠ ·)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.splitParts k xs (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts) = parts := by
  induction xs generalizing parts with
  | nil =>
    have hp : parts = [] := List.length_eq_zero_iff.mp (by simpa only [List.count_nil] using hc)
    subst parts
    rfl
  | cons a xs ih =>
    by_cases ha : a = k
    · subst a
      cases parts with
      | nil => simp only [List.length_nil, List.count_cons_self] at hc; omega
      | cons part parts =>
        have ht : parts.length = xs.count k := by simpa only [List.length_cons,
          List.count_cons_self, Nat.add_right_cancel_iff] using hc
        have hh := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.substitute_head_not_inserted k xs parts hx
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl, List.headD_cons, List.tail_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.splitParts,
          ite_eq_left rfl, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.takeWhile_inserted_append k part _ hh,
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.dropWhile_inserted_append k part _ hh, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_filterMap_inserted, ih parts ht hx.tail]
    · have ht : parts.length = xs.count k := by simpa [ha] using hc
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right ha, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.splitParts, ite_eq_right ha, List.tail_cons,
        ih parts ht hx.tail]

/-- 概要：実際の合成語から元の重なる分割の全部分語を復元できる（BF §1.5.9）。
方針：元の外側語の非退化性と部分語個数を復元公式へ渡す。
規約：内側語長零の分割も許す。
使われ方：分割の長さと添字の一意性を証明する。 -/
lemma splitParts_compositeWord {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.splitParts k (List.ofFn u.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r) = r.segments v.val := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.splitParts_substitute k (List.ofFn u.val) (r.segments v.val)
    (by rw [r.segments_length]; rfl) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.isChain_ofFn_of_nondegenerate u.val u.nondegenerate)

/-- 概要：同じ元の両語から同じ合成語を与える分割は等しい（BF §1.5.9）。
方針：復元した全部分語列の長さを比較し、有限な各部分長へ戻す。
規約：正の内側語長を要求しない。
使われ方：合成項の全単射で分割添字を一意に決める。 -/
lemma partition_unique {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r r' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e))
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r') : r = r' := by
  have hp := congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.splitParts k (List.ofFn u.val)) he
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.splitParts_compositeWord, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.splitParts_compositeWord] at hp
  have hl := congrArg (fun ps => ps.map List.length) hp
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segments, List.map_ofFn, Function.comp_def,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segment_length] at hl
  have hf := List.ofFn_injective hl
  apply Subtype.ext
  funext i
  exact Fin.ext (congrFun hf i)

/-- 概要：正の内側語長で元の両語と分割の全データは合成語から一意（BF §1.5.9）。
方針：元の両語の復元で語を揃えてから分割の復元を使う。
規約：分割型は外側語に依存するため分割の比較は HEq で記す。
使われ方：全合成項の対応の単射性。 -/
lemma inputs_partition_unique {m n d e : ℕ}
    (u u' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v v' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e))
    (r' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u'.val k) (n + e))
    (hl : 0 < n + e) (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u' v' k r') :
    u = u' ∧ v = v' ∧ HEq r r' := by
  obtain ⟨hu, hv⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.input_words_unique u u' v v' k r r' hl he
  subst u'
  subst v'
  exact ⟨rfl, rfl, heq_of_eq (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.partition_unique u v k r r' he)⟩

/-- 概要：合成語だけから元の外側語を復元して全分割部分語を取り出す（BF §1.5.9）。
方針：出力からの外側語の復元を部分語復元の案内として使う。
規約：元の二語や分割は入力にしない。
使われ方：合成項の逆写像の計算可能な部分語成分。 -/
def partsOfWord {m n : ℕ} (k : Fin (m + 1)) (out : List (Fin (m + n))) :
    List (List (Fin n)) := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.splitParts k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out) out

/-- 概要：正の内側語長の実際の合成語だけから全分割成分を復元（BF §1.5.9）。
方針：外側語の一般の復元を案内に元の全部分語を取り出す。
規約：元の両語と分割を逆写像に渡さない。
使われ方：逆構成で得る分割と元の分割の照合。 -/
lemma partsOfWord_compositeWord {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hl : 0 < n + e) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.partsOfWord k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord u v k r) = r.segments v.val := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.partsOfWord, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord_compositeWord u v k r hl, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.splitParts_compositeWord]

/-- 概要：正の内側語長で元の語対と分割を合成語へ送る関数は単射（BF §1.5.9）。
方針：同じ出力から元の両語を揃え、全分割部分語の復元で分割を揃える。
規約：元の語と分割は依存対で添字づける。
使われ方：一般の TR 合成保存で全項の対応の単射性を供給する。 -/
lemma composite_data_injective {m n d e : ℕ} (k : Fin (m + 1)) (hl : 0 < n + e) :
    Function.Injective (fun z : Σ u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d,
      Σ _v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e) =>
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord z.1 z.2.1 k z.2.2) := by
  rintro ⟨u, v, r⟩ ⟨u', v', r'⟩ he
  obtain ⟨hu, hv⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.input_words_unique u u' v v' k r r' hl he
  subst u'
  subst v'
  have hr := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.partition_unique u v k r r' he
  subst r'
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
