module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CanonicalReduction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CanonicalForcedLength

/-!
模型。文献の定義との比較は後で
# 標準 table の非退化項の一意性

概要：Berger–Fresse §1.4.3 の標準頂点列からの非退化出力を持つ行長の選択は唯一。
方針：後続行に対する行長の強制を反復し、最後の長さを Schedule の総和で決める。
規約：非退化性は出力リストの隣接非一致として述べる。
使われ方：TR の有限和を標準 Schedule の一項へ帰着する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：非退化な後続出力では最後以外の全行長が標準値（BF §1.4.3）。
方針：現在行の長さを強制して除外状態を更新し、後続の主張へ移る。
規約：行長の総和条件をまだ使わない。
使われ方：Schedule 全体の一意性の前半を証明する。 -/
lemma wordRows_lengths_forced_from {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (r : Fin (d + 1) → ℕ) (i : Fin (d + 1)) :
    ∀ out : List (Fin n),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.wordRows v r).drop i.val)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i)) = some out →
      out.IsChain (· ≠ ·) →
      ∀ j : Fin d, i.val ≤ j.val → r j.castSucc = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalLengths v j.castSucc := by
  induction i using Fin.reverseInduction with
  | last =>
    intro out h hc j hj
    have hb := j.isLt
    simp only [Fin.val_last] at hj
    omega
  | cast i ih =>
    intro out h hc j hj
    have hsingle := h
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.wordRows_drop_cons v r i.castSucc] at hsingle
    have hpair := hsingle
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc), r i.castSucc) ::
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.wordRows v r).drop i.succ.val)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc)) = some out at hpair
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.wordRows_drop_cons v r i.succ] at hpair
    have hlen := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRows_force_length v i _ _ _ out hpair hc
    by_cases hij : j = i
    · subst j
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalLengths_castSucc] using hlen
    · obtain ⟨_, _, tail, ht, he⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ hsingle
      rw [hlen] at ht
      simp only [Nat.add_sub_cancel] at ht
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRows_exclusion_update] at ht
      have hctail : tail.IsChain (· ≠ ·) := by
        rw [he] at hc
        exact hc.right_of_append
      apply ih tail ht hctail j
      have hne : i.val ≠ j.val := fun hval => hij (Fin.ext hval.symm)
      change i.val + 1 ≤ j.val
      change i.val ≤ j.val at hj
      omega

/-- 概要：標準頂点列の非退化出力を持つ Schedule は標準 Schedule（BF §1.4.3）。
方針：最後以外の長さの一致と総和条件を使い、最後の長さも一致させる。
規約：標準 Schedule の構成に正の arity を用いる。
使われ方：他の Schedule の TR 項を全て零にする。 -/
lemma schedule_eq_canonical_of_isChain {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (hn : 0 < n)
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalVertices v) r) [] = some out)
    (hc : out.IsChain (· ≠ ·)) : r = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalSchedule v hn := by
  have hf := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.wordRows_lengths_forced_from v (fun i => (r.val i).val) 0 out
  have hfirst : ∀ j : Fin d, (r.val j.castSucc).val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalLengths v j.castSucc := by
    intro j
    apply hf _ hc j (Nat.zero_le _)
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_canonical_eq_wordRows, Fin.val_zero, List.drop_zero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart_zero,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.pastFinals, List.take_zero, List.dedup_nil, List.filter_nil] using h
  apply Subtype.ext
  funext i
  apply Fin.ext
  change (r.val i).val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalLengths v i
  cases i using Fin.lastCases with
  | cast i => exact hfirst i
  | last =>
    have hr := r.property.2
    have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalLengths_sum v
    rw [Fin.sum_univ_castSucc] at hr hs
    have he : (∑ i : Fin d, (r.val i.castSucc).val) =
        ∑ i : Fin d, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalLengths v i.castSucc :=
      Finset.sum_congr rfl (fun i _ => hfirst i)
    omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
