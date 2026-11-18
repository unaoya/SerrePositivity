module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ShuffleInnerRecovery
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentTraceSplit

/-!
模型。文献の定義との比較は後で
# 全内側表の復元で非最終行末の再出現を保つ

概要：Berger–Fresse §1.5.8 の逆構成で、元の合成 Schedule の行末再出現を内側へ移す。
方針：実際の水平分割で帰納し、垂直直前の保持末尾の再出現先を後続の内側復元語へ戻す。
規約：個々の水平行の内側選択が空でもよく、行長総和は仮定しない。
使われ方：全射性と合わせて元の内側次数の Schedule 総和を証明する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：残る元の末尾は復元内側語の同じ末尾となる（BF §1.5.8）。
方針：末尾一文字を分離して射影し、縮約の末尾保存を使う。
規約：末尾より前の文字は射影で捨ててもよい。
使われ方：実際の非最終行末の再出現を復元内側行末へ移す。 -/
lemma innerWord_getLast?_of_retained {m n : ℕ} (k : Fin (m + 1))
    (xs : List (Fin (m + n))) (a : Fin (m + n)) (b : Fin n)
    (ha : xs.getLast? = some a) (hf : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k a = some b) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k xs).getLast? = some b := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_getLast?]
  obtain ⟨pre, rfl⟩ := List.getLast?_eq_some_iff.mp ha
  simp only [List.filterMap_append, List.filterMap_cons, hf, List.filterMap_nil,
    List.getLast?_append, List.getLast?_singleton, Option.some_or]

/-- 概要：水平区間分割による全内側表の復元は非最終行末の再出現を保つ（BF §1.5.8）。
方針：垂直直前の実際の行末を元の再出現条件で後続へ移し、内側部分単射射影で戻す。
規約：再出現条件は元の実際の証跡にだけ要求し、復元行長総和は仮定しない。
使われ方：成功した元の合成 Schedule から内側 Schedule の余剰総和を導く。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.InnerRunDecomposition.inner_recurrent {m n : ℕ}
    {entries : List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ)}
    {sources : List (Equiv.Perm (Fin n))} (hd : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.InnerRunDecomposition entries sources)
    (k : Fin (m + 1)) (removed out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k entries) removed = some out) (hc : out.IsChain (· ≠ ·))
    (hne : out.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) ≠ [])
    (hrec : ∀ picked, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k entries) removed picked →
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds picked) :
    ∃ table : List (List (Fin n) × ℕ), ∃ selected : List (List (Fin n)),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace table (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) selected ∧
      table.map Prod.fst = sources.map (fun τ => List.ofFn τ.symm) ∧
      selected.flatten = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k out ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds selected := by
  induction hd generalizing removed out with
  | single τ before σ r =>
    obtain ⟨table, hm, hs⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.InnerRunDecomposition.single τ before σ r).inner_success
      k removed out h hc hne
    obtain ⟨picked, hp, hf⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionTrace_of_reduceRows table _ _ hs
    have hlen : picked.length = 1 := by
      have ht := congrArg List.length hm
      simp only [List.length_map, List.length_cons, List.length_nil] at ht
      rw [hp.length, ht]
    obtain ⟨word, hw⟩ := List.length_eq_one_iff.mp hlen
    rw [hw] at hp hf
    exact ⟨table, [word], hp, hm, hf, by simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds]⟩
  | step τ τ' hneq before σ r s rest sources hd ih =>
    have hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows τ k before ++
          (List.ofFn (permutationComposition m n k σ τ).symm, r) ::
          (List.ofFn (permutationComposition m n k σ τ').symm, s) :: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k rest)
        removed = some out := by
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows, List.map_append, List.map_map,
        Function.comp_def, List.map_cons] using h
    have hrFull : ∀ picked, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows τ k before ++
          (List.ofFn (permutationComposition m n k σ τ).symm, r) ::
          (List.ofFn (permutationComposition m n k σ τ').symm, s) :: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k rest)
        removed picked → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds picked := by
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows, List.map_append, List.map_map,
        Function.comp_def, List.map_cons] using hrec
    obtain ⟨picked, middle, tail, hp, ht, ho⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionPrefix_of_reduceRows
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows τ k before) _ removed out hs
    have hrTail := hp.recurrent_tail hrFull
    have hcTail : tail.IsChain (· ≠ ·) := by rw [ho] at hc; exact hc.right_of_append
    obtain ⟨hr, hb, post, hpost, htail⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ ht
    let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available middle (List.ofFn (permutationComposition m n k σ τ).symm)
    let rem := middle ++ xs.take (r - 1)
    have hpOne : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix [(List.ofFn (permutationComposition m n k σ τ).symm, r)]
        middle [xs.take r] rem := .cons hr hb (.nil _)
    have hrPost := hpOne.recurrent_tail hrTail
    have hcPost : post.IsChain (· ≠ ·) := by rw [htail] at hcTail; exact hcTail.right_of_append
    have hjoin := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.vertical_inner_join k σ τ τ' r s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k rest) middle picked.flatten
      post (by rw [← htail]; exact ht) (by rw [← htail]; exact hcTail)
    obtain ⟨table, selected, htrace, hmatrix, hflat, hrecur⟩ :=
      ih _ _ hpost hcPost hjoin.2 hrPost
    obtain ⟨t, hfirst⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontal_inner_before_vertical τ τ' k before σ r s removed middle
      tail picked (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k rest) hp ht hcTail
    obtain ⟨rawPicked, hraw, hrawFlat⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionTrace_of_reduceRows _ _ _ hpost
    have hrawNonempty : rawPicked ≠ [] := by
      intro he
      have hl := hraw.length
      rw [he] at hl
      simp only [List.length_nil, List.length_cons] at hl
      omega
    have hcurrentRec := hrTail _ (.cons hr hb hraw)
    obtain ⟨a, b, hlast, hf⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_vertical_last_retained σ τ τ' k
      middle _ r s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k rest) ht hcTail
    have ha : a ∈ post := by
      rw [← hrawFlat]
      exact hcurrentRec.getLast?_mem hrawNonempty a hlast
    have hlastPre : (picked.flatten ++ xs.take r).getLast? = some a := by
      rw [List.getLast?_append, hlast, Option.some_or]
    have hend := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord_getLast?_of_retained k (picked.flatten ++ xs.take r) a b hlastPre hf
    have he : out = (picked.flatten ++ xs.take r) ++ post := by
      rw [ho, htail, List.append_assoc]
    have hword := congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k) he
    rw [hjoin.1] at hword
    refine ⟨(List.ofFn τ.symm, t) :: table, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k (picked.flatten ++ xs.take r) :: selected,
      ?_, ?_, ?_, ?_⟩
    · simpa only [List.singleton_append] using hfirst.trace_append htrace
    · simp only [List.map_cons, hmatrix]
    · simpa only [List.flatten_cons, hflat] using hword.symm
    · refine ⟨?_, hrecur⟩
      intro hneFirst _
      have heLast : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k (picked.flatten ++ xs.take r)).getLast hneFirst = b := by
        rw [List.getLast?_eq_some_getLast hneFirst] at hend
        exact Option.some.inj hend
      rw [heLast, hflat]
      apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mem_innerWord k b post).mpr
      rwa [← (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_eq_some_iff k a b).mp hf]

/-- 概要：軸方向の全合成表から再出現を持つ実際の内側抽出証跡を得る（BF §1.5.8）。
方針：具体的な水平分割を作り、全内側復元の再出現条件と元の行列を返す。
規約：元の全証跡の再出現条件だけを入力とし、内側の総和条件は仮定しない。
使われ方：元の内側 Schedule の余剰総和を全射性から計算する。 -/
lemma inner_recurrent_table_success {m n : ℕ} (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ))
    (removed out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k entries) removed = some out) (hc : out.IsChain (· ≠ ·))
    (haxis : entries.IsChain (fun p q => p.1 = q.1 ∨ p.2.1 = q.2.1))
    (hne : out.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) ≠ [])
    (hrec : ∀ picked, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k entries) removed picked →
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds picked) :
    ∃ table : List (List (Fin n) × ℕ), ∃ selected : List (List (Fin n)),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace table (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) selected ∧
      table.map Prod.fst = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (entries.map (fun p => p.2.1))).map
        (fun τ => List.ofFn τ.symm) ∧
      selected.flatten = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k out ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds selected := by
  cases entries with
  | nil =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable, List.map_nil, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_nil, Option.some.injEq] at h
    subst out
    exact (hne rfl).elim
  | cons entry rest =>
    obtain ⟨σ, τ, r⟩ := entry
    obtain ⟨sources, hd⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerRunDecomposition_exists σ τ r rest haxis
    obtain ⟨table, selected, ht, hm, hf, hr⟩ := hd.inner_recurrent k removed out h hc hne hrec
    exact ⟨table, selected, ht,
      hm.trans (congrArg (List.map (fun τ => List.ofFn τ.symm)) hd.sources_eq).symm, hf, hr⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
