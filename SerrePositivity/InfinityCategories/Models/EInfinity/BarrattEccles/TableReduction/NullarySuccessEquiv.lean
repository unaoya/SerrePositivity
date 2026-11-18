module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapTraceUniqueness
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NullaryProjectedTable
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NullarySuccessMap

/-!
模型。文献の定義との比較は後で
# 空語合成の成功項の有限全単射

概要：Berger–Fresse §1.5.7–9 の nullary 次数零で実際の成功項の全単射を構成する。
方針：同じ削除出力の射影選択行列を揃え、保持末尾から元の全成功語を一意に戻す。
規約：出力 arity は正。失敗・退化・複数出現の零項は後で有限和へ戻す。
使われ方：空語挿入の一般の TR 合成保存の全成功項の対応。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：同じ削除出力を持つ元の指定値一出現の成功出力は一致（BF §1.5.7–9）。
方針：実際の射影表の一意性と保持末尾による元の抽出一意性を連結する。
規約：出力の非退化性は要求しない。出力 arity は正。
使われ方：nullary 成功項の順方向写像の単射性。 -/
lemma nullary_success_output_unique {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1))
    (s s' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 1) d) (out out' : List (Fin (m + 1)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) [] = some out) (h' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s') [] = some out')
    (hc : out.count k = 1) (hc' : out'.count k = 1)
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k out = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k out') : out = out' := by
  obtain ⟨picked, ht, hout⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionTrace_of_reduceRows _ _ _ h
  obtain ⟨picked', ht', hout'⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionTrace_of_reduceRows _ _ _ h'
  have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullary_projected_selected_eq hm w 1 k s s' picked picked' ht ht'
    (by rw [hout]; exact hc) (by rw [hout']; exact hc') (by rw [hout, hout']; exact he)
  have hr := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullary_trace_ready hm w k s picked ht (by rw [hout]; exact hc)
  have hr' := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullary_trace_ready hm w k s' picked' ht' (by rw [hout']; exact hc')
  have hmats : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s).map Prod.fst = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s').map Prod.fst := by
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.map_ofFn, Function.comp_def]
  have hsize : picked.flatten.length = picked'.flatten.length := by
    rw [hout, hout', _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w s out h, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w s' out' h']
  have heq := ht.eq_of_filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel_partial_injective k)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_nodup w s) hr _ _ ht' hmats hp hsize hr'
  rw [← hout, ← hout', heq]

/-- 概要：nullary 順方向写像は単射（BF §1.5.7–9）。
方針：同じ目標語の元の削除出力を揃え、元の語と Schedule の一意性を適用する。
規約：正の出力 arity の全入力列・全次数。
使われ方：全射性と合わせて有限全単射を作る。 -/
lemma nullaryForward_injective {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1)) : Function.Injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullaryForward hm w τ k) := by
  intro p q he
  have hword := congrArg (fun v => List.ofFn v.val.2.val) he
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullaryForward_word, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullaryForward_word] at hword
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.successfulWord_eq_of_word_eq w p.val q.val
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullary_success_output_unique hm w k p.val.val.1 q.val.val.1 _ _
    p.val.property q.val.property p.property.1 q.property.1 hword

/-- 概要：元の非零候補と実際の nullary 目標成功項の有限全単射（BF §1.5.7–9）。
方針：同じ削除出力の元の一意性と解放値探索による全射性を使う。
規約：正の出力 arity。本来の全次数を保つ。
使われ方：空語合成の全有限和を元の部分合成の和へ移す。 -/
def nullarySuccessEquiv {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NullarySource w k ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulWord (fun j => permutationComposition m 0 k (w j) τ) :=
  Equiv.ofBijective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullaryForward hm w τ k)
    ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullaryForward_injective hm w τ k, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullaryForward_surjective hm w τ k⟩

/-- 概要：nullary の全成功基底和は元の非零候補の空語合成の和（BF §1.5.7–9）。
方針：有限全単射で添字を移し、各項の値の保存を使う。
規約：任意の可換環。失敗・退化の零項はこの和の外に置く。
使われ方：全 onSequence の合成保存へ戻す成功項の和の等式。 -/
lemma sum_nullary_source_eq_target (A : Type u) [CommRing A] {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1)) :
    (∑ p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NullarySource w k,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords A p.val.val.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord (1 : Equiv.Perm (Fin 0))) k) =
      ∑ q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulWord (fun j => permutationComposition m 0 k (w j) τ),
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A (m + 0) (d + 0) (ULift.up q.val.2) := by
  apply Fintype.sum_equiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullarySuccessEquiv hm w τ k)
  intro p
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullaryForward_term A hm w τ k p

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
