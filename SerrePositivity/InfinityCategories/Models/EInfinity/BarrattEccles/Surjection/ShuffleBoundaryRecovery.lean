module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.OutputTraceUniqueness
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.InsertedBoundary
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleStepMembership

/-!
模型。文献の定義との比較は後で
# 実際の選択行列から shuffle の各辺を復元

概要：Berger–Fresse §1.5.8 の逆構成で、成功出力の行境界だけから垂直辺を判定する。
方針：指定行まで実際の抽出を再開し、垂直・水平境界の内側性を適用する。
規約：元の両置換列の単射性や元の経路の一致を仮定しない。
使われ方：同じ非退化出力を持つ二つの経路の一意性。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：指定行境界の両文字がともに内側となる条件（BF §1.5.8）。
方針：実際の二選択行を Option で取り、挿入された両端文字の存在を要求する。
規約：行が足りない場合は偽。
使われ方：元の入力置換列に依存しない辺方向の判定。 -/
def BoundaryInserted {m n : ℕ} (k : Fin (m + 1))
    (picked : List (List (Fin (m + n)))) (i : ℕ) : Prop :=
  ∃ left right, picked[i]? = some left ∧ picked[i + 1]? = some right ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.InsertedJoin k left right

/-- 概要：実際の非退化成功では内側二端の行境界と垂直辺が同値（BF §1.5.8）。
方針：指定辺での二行を抽出証跡から取り出し、水平・垂直の一般境界補題で判定する。
規約：元の成功出力の非退化性だけを要求し、両入力の非退化性は仮定しない。
使われ方：全成功経路の辺集合を同じ選択行列から一意に復元する。 -/
lemma boundaryInserted_iff_notMem {m n d e : ℕ} (k : Fin (m + 1)) (s : ShufflePath d e)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e))
    (picked : List (List (Fin (m + n))))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => permutationComposition m n k (outer (s.horizontal j))
      (inner (s.vertical j))) r) [] picked) (hc : picked.flatten.IsChain (· ≠ ·))
    (i : Fin (d + e)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.BoundaryInserted k picked i.val ↔ i ∉ s.val := by
  let w := fun j => permutationComposition m n k (outer (s.horizontal j)) (inner (s.vertical j))
  obtain ⟨removed, hd⟩ := h.drop i.val
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_drop_two w r i] at hd
  generalize hsel : picked.drop i.val = selected at hd
  cases hd with
  | @cons _ _ _ _ nextPicked hr hb hnext =>
    cases hnext with
    | @cons _ _ _ _ restPicked hs hsb hrest =>
      let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (w i.castSucc).symm)
      let rem := removed ++ xs.take ((r.val i.castSucc).val - 1)
      let ys := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available rem (List.ofFn (w i.succ).symm)
      have hp0 : picked[i.val]? = some (xs.take (r.val i.castSucc).val) := by
        have he := congrArg (fun words : List (List (Fin (m + n))) => words[0]?) hsel
        simpa only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] using he
      have hp1 : picked[i.val + 1]? = some (ys.take (r.val i.succ).val) := by
        have he := congrArg (fun words : List (List (Fin (m + n))) => words[1]?) hsel
        simpa only [List.getElem?_drop, List.getElem?_cons_succ, List.getElem?_cons_zero] using he
      have hlocal : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
          ((List.ofFn (w i.castSucc).symm, (r.val i.castSucc).val) ::
            (List.ofFn (w i.succ).symm, (r.val i.succ).val) ::
              (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).drop (i.val + 2)) removed = some (picked.drop i.val).flatten := by
        rw [hsel]
        exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace.cons hr hb (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace.cons hs hsb hrest)).reduceRows
      have hlocalChain := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.flatten_drop_isChain picked i.val hc
      have hjoin : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.BoundaryInserted k picked i.val ↔
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.InsertedJoin k (xs.take (r.val i.castSucc).val) (ys.take (r.val i.succ).val) := by
        constructor
        · rintro ⟨left, right, hl, hr, hj⟩
          have heL : left = xs.take (r.val i.castSucc).val := Option.some.inj (hl.symm.trans hp0)
          have heR : right = ys.take (r.val i.succ).val := Option.some.inj (hr.symm.trans hp1)
          subst left
          subst right
          exact hj
        · intro hj
          exact ⟨_, _, hp0, hp1, hj⟩
      rw [hjoin]
      by_cases hm : i ∈ s.val
      · have hf := (s.step_of_mem i hm).2
        have hl : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
            ((List.ofFn (permutationComposition m n k (outer (s.horizontal i.castSucc))
              (inner (s.vertical i.castSucc))).symm, (r.val i.castSucc).val) ::
              (List.ofFn (permutationComposition m n k (outer (s.horizontal i.succ))
                (inner (s.vertical i.castSucc))).symm, (r.val i.succ).val) ::
                  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).drop (i.val + 2)) removed = some (picked.drop i.val).flatten := by
          simpa only [w, hf] using hlocal
        have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.horizontal_not_inserted_join k (outer (s.horizontal i.castSucc))
          (outer (s.horizontal i.succ)) (inner (s.vertical i.castSucc))
          (r.val i.castSucc).val (r.val i.succ).val ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).drop (i.val + 2))
          removed _ hl hlocalChain
        have hn' : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.InsertedJoin k (xs.take (r.val i.castSucc).val)
            (ys.take (r.val i.succ).val) := by simpa only [xs, ys, rem, w, hf] using hn
        exact ⟨fun hj => (hn' hj).elim, fun hh => (hh hm).elim⟩
      · have hf := (s.step_of_notMem i hm).1
        have hl : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
            ((List.ofFn (permutationComposition m n k (outer (s.horizontal i.castSucc))
              (inner (s.vertical i.castSucc))).symm, (r.val i.castSucc).val) ::
              (List.ofFn (permutationComposition m n k (outer (s.horizontal i.castSucc))
                (inner (s.vertical i.succ))).symm, (r.val i.succ).val) ::
                  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).drop (i.val + 2)) removed = some (picked.drop i.val).flatten := by
          simpa only [w, hf] using hlocal
        have hj := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.vertical_inserted_join k (outer (s.horizontal i.castSucc))
          (inner (s.vertical i.castSucc)) (inner (s.vertical i.succ))
          (r.val i.castSucc).val (r.val i.succ).val ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).drop (i.val + 2))
          removed _ hl hlocalChain
        have hj' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.InsertedJoin k (xs.take (r.val i.castSucc).val)
            (ys.take (r.val i.succ).val) := by simpa only [xs, ys, rem, w, hf] using hj
        exact ⟨fun _ => hm, fun _ => hj'⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
