module

public import SerrePositivity.EInfinity.TableReduction.FilterMapTraceUniqueness
public import SerrePositivity.EInfinity.TableReduction.NullaryProjectedTable
public import SerrePositivity.EInfinity.TableReduction.NullarySuccessMap

/-!
# 空語合成の成功項の有限全単射

概要：Berger–Fresse §1.5.7–9 の nullary 次数零で実際の成功項の全単射を構成する。
方針：同じ削除出力の射影選択行列を揃え、保持末尾から元の全成功語を一意に戻す。
規約：出力 arity は正。失敗・退化・複数出現の零項は後で有限和へ戻す。
使われ方：空語挿入の一般の TR 合成保存の全成功項の対応。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.TableReduction

open Surjection BarrattEccles

/-- 概要：同じ削除出力を持つ元の指定値一出現の成功出力は一致（BF §1.5.7–9）。
方針：実際の射影表の一意性と保持末尾による元の抽出一意性を連結する。
規約：出力の非退化性は要求しない。出力 arity は正。
使われ方：nullary 成功項の順方向写像の単射性。 -/
lemma nullary_success_output_unique {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1))
    (s s' : Schedule (m + 1) d) (out out' : List (Fin (m + 1)))
    (h : reduceRows (rows w s) [] = some out) (h' : reduceRows (rows w s') [] = some out')
    (hc : out.count k = 1) (hc' : out'.count k = 1)
    (he : eraseSlotWord k out = eraseSlotWord k out') : out = out' := by
  obtain ⟨picked, ht, hout⟩ := extractionTrace_of_reduceRows _ _ _ h
  obtain ⟨picked', ht', hout'⟩ := extractionTrace_of_reduceRows _ _ _ h'
  have hp := nullary_projected_selected_eq hm w 1 k s s' picked picked' ht ht'
    (by rw [hout]; exact hc) (by rw [hout']; exact hc') (by rw [hout, hout']; exact he)
  have hr := nullary_trace_ready hm w k s picked ht (by rw [hout]; exact hc)
  have hr' := nullary_trace_ready hm w k s' picked' ht' (by rw [hout']; exact hc')
  have hmats : (rows w s).map Prod.fst = (rows w s').map Prod.fst := by
    simp only [rows, List.map_ofFn, Function.comp_def]
  have hsize : picked.flatten.length = picked'.flatten.length := by
    rw [hout, hout', output_length w s out h, output_length w s' out' h']
  have heq := ht.eq_of_filterMap (eraseSlotLabel k) (eraseSlotLabel_partial_injective k)
    (rows_nodup w s) hr _ _ ht' hmats hp hsize hr'
  rw [← hout, ← hout', heq]

/-- 概要：nullary 順方向写像は単射（BF §1.5.7–9）。
方針：同じ目標語の元の削除出力を揃え、元の語と Schedule の一意性を適用する。
規約：正の出力 arity の全入力列・全次数。
使われ方：全射性と合わせて有限全単射を作る。 -/
lemma nullaryForward_injective {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1)) : Function.Injective (nullaryForward hm w τ k) := by
  intro p q he
  have hword := congrArg (fun v => List.ofFn v.val.2.val) he
  rw [nullaryForward_word, nullaryForward_word] at hword
  apply Subtype.ext
  apply successfulWord_eq_of_word_eq w p.val q.val
  exact nullary_success_output_unique hm w k p.val.val.1 q.val.val.1 _ _
    p.val.property q.val.property p.property.1 q.property.1 hword

/-- 概要：元の非零候補と実際の nullary 目標成功項の有限全単射（BF §1.5.7–9）。
方針：同じ削除出力の元の一意性と解放値探索による全射性を使う。
規約：正の出力 arity。本来の全次数を保つ。
使われ方：空語合成の全有限和を元の部分合成の和へ移す。 -/
def nullarySuccessEquiv {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1)) :
    NullarySource w k ≃ SuccessfulWord (fun j => permutationComposition m 0 k (w j) τ) :=
  Equiv.ofBijective (nullaryForward hm w τ k)
    ⟨nullaryForward_injective hm w τ k, nullaryForward_surjective hm w τ k⟩

/-- 概要：nullary の全成功基底和は元の非零候補の空語合成の和（BF §1.5.7–9）。
方針：有限全単射で添字を移し、各項の値の保存を使う。
規約：任意の可換環。失敗・退化の零項はこの和の外に置く。
使われ方：全 onSequence の合成保存へ戻す成功項の和の等式。 -/
lemma sum_nullary_source_eq_target (A : Type u) [CommRing A] {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1)) :
    (∑ p : NullarySource w k,
      compositionOnWords A p.val.val.2 (permutationWord (1 : Equiv.Perm (Fin 0))) k) =
      ∑ q : SuccessfulWord (fun j => permutationComposition m 0 k (w j) τ),
        basis A (m + 0) (d + 0) (ULift.up q.val.2) := by
  apply Fintype.sum_equiv (nullarySuccessEquiv hm w τ k)
  intro p
  exact nullaryForward_term A hm w τ k p

end SerrePositivity.EInfinity.TableReduction
