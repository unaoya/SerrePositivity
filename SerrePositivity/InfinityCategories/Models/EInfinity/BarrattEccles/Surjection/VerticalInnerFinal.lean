module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.VerticalInnerStep
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapFinal
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.PrefixExclusions

/-!
模型。文献の定義との比較は後で
# 垂直最終行の内側部分の抽出

概要：Berger–Fresse §1.5.8 の垂直成分の最終選択語を内側区間の末尾へ戻す。
方針：直前の垂直行から内側先頭を得て射影の非空性を示し、内側末尾を残して切る。
規約：元の合成行の終状態とは分け、復元した内側区間の共有末尾を残す。
使われ方：合成表の逆構成で垂直成分を端点付きの内側抽出にする。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

/-- 概要：任意の合成行の非空内側選択語を元の内側最終行で抽出する（BF §1.5.8）。
方針：任意の除外状態で一行を射影し、実際の元の内側逆置換行へ戻す。
規約：行長は射影語長であり、内側の末尾一文字を除外せず残す。
使われ方：垂直成分の最終行が外側文字で終わる場合にも適用する。 -/
lemma permutationComposition_inner_final_step {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n))
    (k : Fin (m + 1)) (removed : List (Fin (m + n))) (r : ℕ)
    (hn : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
      (List.ofFn (permutationComposition m n k σ τ).symm)).take r).filterMap
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) ≠ []) :
    let picked := ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
      (List.ofFn (permutationComposition m n k σ τ).symm)).take r).filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix [(List.ofFn τ.symm, picked.length)] (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k))
      [picked] (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) ++ picked.take (picked.length - 1)) := by
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMap_final_prefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_partial_injective k)
    removed (List.ofFn (permutationComposition m n k σ τ).symm) r hn
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_permutationComposition_row] using ht

/-- 概要：非退化な成功垂直二行の後行の内側選択語は非空（BF §1.5.8）。
方針：正の行長から実際の先頭を取り出し、前行から得た内側先頭制約を適用する。
規約：後行が垂直成分の最終行でもよい。
使われ方：最終行の内側抽出に必要な正の行長を元の成功から供給する。 -/
lemma permutationComposition_vertical_next_inner_nonempty {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (τ τ' : Equiv.Perm (Fin n))
    (k : Fin (m + 1)) (removed out : List (Fin (m + n)))
    (r s : ℕ) (rest : List (List (Fin (m + n)) × ℕ))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
      ((List.ofFn (permutationComposition m n k σ τ).symm, r) ::
        (List.ofFn (permutationComposition m n k σ τ').symm, s) :: rest)
      removed = some out) (hc : out.IsChain (· ≠ ·)) :
    let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm)
    let rem := removed ++ xs.take (r - 1)
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available rem (List.ofFn (permutationComposition m n k σ τ').symm)).take s).filterMap
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) ≠ [] := by
  obtain ⟨hr, hb, tail, ht, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
  obtain ⟨hs, hsb, _, _, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ ht
  let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm)
  let rem := removed ++ xs.take (r - 1)
  let ys := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available rem (List.ofFn (permutationComposition m n k σ τ').symm)
  have hi : r - 1 < xs.length := by change r ≤ xs.length at hb; omega
  have hj : 0 < ys.length := by change s ≤ ys.length at hsb; omega
  let a := xs[r - 1]
  let b := ys[0]
  have he : xs[r - 1]? = some a := List.getElem?_eq_getElem hi
  have hh : ys.head? = some b := by
    rw [List.head?_eq_getElem?]
    exact List.getElem?_eq_getElem hj
  obtain ⟨c, hb'⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_vertical_next_head_inserted
    σ τ τ' k removed out a b r s rest he hh h hc
  have hmem : b ∈ ys.take s := by
    obtain ⟨ys', hy⟩ := List.head?_eq_some_iff.mp hh
    cases s with
    | zero => omega
    | succ s => rw [hy, List.take_succ_cons]; exact List.mem_cons_self
  have hc' : c ∈ (ys.take s).filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) :=
    List.mem_filterMap.mpr ⟨b, hmem, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_eq_some_iff k b c).mpr hb'⟩
  change (ys.take s).filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) ≠ []
  intro hn
  rw [hn] at hc'
  exact List.not_mem_nil hc'

/-- 概要：成功垂直二行は最後の内側末尾を残す内側二行の抽出を与える（BF §1.5.8）。
方針：前行の終状態を保つ射影と、非空な後行の内側最終抽出を連結する。
規約：選択語は元の二行の内側射影。終状態は最後の内側文字を残す。
使われ方：最小の垂直成分全体を元の内側表の区間として復元する。 -/
lemma permutationComposition_vertical_inner_pair {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (τ τ' : Equiv.Perm (Fin n))
    (k : Fin (m + 1)) (removed out : List (Fin (m + n)))
    (r s : ℕ) (rest : List (List (Fin (m + n)) × ℕ))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
      ((List.ofFn (permutationComposition m n k σ τ).symm, r) ::
        (List.ofFn (permutationComposition m n k σ τ').symm, s) :: rest)
      removed = some out) (hc : out.IsChain (· ≠ ·)) :
    let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm)
    let rem := removed ++ xs.take (r - 1)
    let first := (xs.take r).filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)
    let last := ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available rem
      (List.ofFn (permutationComposition m n k σ τ').symm)).take s).filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix [(List.ofFn τ.symm, first.length), (List.ofFn τ'.symm, last.length)]
      (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) [first, last]
      (rem.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) ++ last.take (last.length - 1)) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_vertical_inner_step σ τ τ' k removed out r s rest h hc
  have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_vertical_next_inner_nonempty σ τ τ' k removed out r s
    rest h hc
  have hq := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_inner_final_step σ τ' k _ s hn
  simpa only [List.cons_append, List.nil_append] using hp.trans hq

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
