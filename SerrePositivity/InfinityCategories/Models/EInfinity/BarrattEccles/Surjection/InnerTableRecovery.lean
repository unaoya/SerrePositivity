module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.InnerRunDecomposition
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.HorizontalInnerRecovery
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.VerticalInnerJoin

/-!
模型。文献の定義との比較は後で
# 成功した全合成表から元の内側表を復元

概要：Berger–Fresse §1.5.8 の逆構成で全水平区間の復元行を接続する。
方針：実際の分割で帰納し、垂直辺での終状態・内側語・後続非空性を同時に渡す。
規約：初期除外は任意。全内側射影が非空であれば最終区間を通常の一行で閉じる。
使われ方：shuffle 経路から元の内側次数の成功 Schedule を構成する前段。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：実際の水平区間分割から全内側表の成功を得る（BF §1.5.8）。
方針：先行水平区間を一行へ戻し、垂直辺の実際の状態で後続の復元表を接続する。
規約：元の内側表の成功は仮定せず、合成表の非退化成功と射影非空性だけから構成する。
使われ方：全合成表を元の内側行列へ戻す逆構成。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.InnerRunDecomposition.inner_success {m n : ℕ}
    {entries : List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ)}
    {sources : List (Equiv.Perm (Fin n))} (hd : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.InnerRunDecomposition entries sources)
    (k : Fin (m + 1)) (removed out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k entries) removed = some out) (hc : out.IsChain (· ≠ ·))
    (hne : out.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) ≠ []) :
    ∃ table : List (List (Fin n) × ℕ),
      table.map Prod.fst = sources.map (fun τ => List.ofFn τ.symm) ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows table (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) = some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k out) := by
  induction hd generalizing removed out with
  | single τ before σ r =>
    have hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows τ k (before ++ [(σ, r)])) removed = some out := by
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows, List.map_append, List.map_map,
        Function.comp_def, List.map_cons, List.map_nil] using h
    obtain ⟨picked, finish, tail, hp, ht, ho⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionPrefix_of_reduceRows
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows τ k (before ++ [(σ, r)])) [] removed out (by simpa using hs)
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_nil, Option.some.injEq] at ht
    subst tail
    simp only [List.append_nil] at ho
    subst out
    obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontal_inner_success τ k (before ++ [(σ, r)]) removed finish picked
      hp hne
    exact ⟨[(List.ofFn τ.symm, s)], rfl, hs⟩
  | step τ τ' hneq before σ r s rest sources hd ih =>
    have hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows τ k before ++
          (List.ofFn (permutationComposition m n k σ τ).symm, r) ::
          (List.ofFn (permutationComposition m n k σ τ').symm, s) :: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k rest)
        removed = some out := by
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows, List.map_append, List.map_map,
        Function.comp_def, List.map_cons] using h
    obtain ⟨picked, middle, tail, hp, ht, ho⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionPrefix_of_reduceRows
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows τ k before) _ removed out hs
    have hcTail : tail.IsChain (· ≠ ·) := by rw [ho] at hc; exact hc.right_of_append
    obtain ⟨hr, hb, post, hpost, htail⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ ht
    have hcPost : post.IsChain (· ≠ ·) := by rw [htail] at hcTail; exact hcTail.right_of_append
    have hjoin := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.vertical_inner_join k σ τ τ' r s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k rest) middle picked.flatten
      post (by rw [← htail]; exact ht) (by rw [← htail]; exact hcTail)
    obtain ⟨table, hmatrix, hsuccess⟩ := ih _ _ hpost hcPost hjoin.2
    obtain ⟨t, hfirst⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontal_inner_before_vertical τ τ' k before σ r s removed middle
      tail picked (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k rest) hp ht hcTail
    have hall := hfirst.append table (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k post) hsuccess
    have he : out = (picked.flatten ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available middle
        (List.ofFn (permutationComposition m n k σ τ).symm)).take r) ++ post := by
      rw [ho, htail, List.append_assoc]
    have hword := congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k) he
    rw [hjoin.1] at hword
    refine ⟨(List.ofFn τ.symm, t) :: table, ?_, ?_⟩
    · simp only [List.map_cons, hmatrix]
    · rw [hword]
      simpa only [List.singleton_append, List.flatten_cons, List.flatten_nil,
        List.append_nil] using hall

/-- 概要：軸方向に進む非退化成功表の全内側復元は実際の抽出成功を持つ（BF §1.5.8）。
方針：具体的な水平区間分割を作り、全内側表の成功と元の行列の縮約表示を合わせる。
規約：射影全体は非空。個々の行の内側射影や水平成分は空でもよい。
使われ方：実際の shuffle 成功を元の内側 TR の成功表へ戻す。 -/
lemma inner_table_success {m n : ℕ} (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ))
    (removed out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k entries) removed = some out) (hc : out.IsChain (· ≠ ·))
    (haxis : entries.IsChain (fun p q => p.1 = q.1 ∨ p.2.1 = q.2.1))
    (hne : out.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) ≠ []) :
    ∃ table : List (List (Fin n) × ℕ),
      table.map Prod.fst = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (entries.map (fun p => p.2.1))).map
        (fun τ => List.ofFn τ.symm) ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows table (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) = some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k out) := by
  cases entries with
  | nil =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable, List.map_nil, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_nil, Option.some.injEq] at h
    subst out
    exact (hne rfl).elim
  | cons entry rest =>
    obtain ⟨σ, τ, r⟩ := entry
    obtain ⟨sources, hd⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerRunDecomposition_exists σ τ r rest haxis
    obtain ⟨table, hm, hs⟩ := hd.inner_success k removed out h hc hne
    exact ⟨table, hm.trans (congrArg (List.map (fun τ => List.ofFn τ.symm)) hd.sources_eq).symm,
      hs⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
