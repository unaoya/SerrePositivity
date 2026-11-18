module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.HorizontalBoundary
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OuterSelection
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapseEndpoints

/-!
模型。文献の定義との比較は後で
# 水平隣接選択語の外側復元の非退化性

概要：Berger–Fresse §1.5.8 の水平二行から復元した二つの外側選択語の連結を扱う。
方針：各選択語は元の外側可用行の非重複な先頭部分で、境界は元の実際の境界に戻る。
規約：全合成出力の非退化性を使い、内側置換を二行で固定する。
使われ方：圧縮外側表の出力の全体の非退化性を復元する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：外側語復元は先頭ラベルを外側へ戻したものを保つ（BF §1.5.8）。
方針：縮約の先頭保存と写像の先頭評価を合成する。
規約：空語では両側とも none。
使われ方：復元した外側選択語の先頭を元の行頭へ戻す。 -/
lemma outerWord_head? {m n : ℕ} (k : Fin (m + 1)) (xs : List (Fin (m + n))) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k xs).head? = xs.head?.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_head?, List.head?_map]

/-- 概要：外側語復元は末尾ラベルを外側へ戻したものを保つ（BF §1.5.8）。
方針：縮約の末尾保存と写像の末尾評価を合成する。
規約：空語では両側とも none。
使われ方：復元した外側選択語の末尾を元の行末へ戻す。 -/
lemma outerWord_getLast? {m n : ℕ} (k : Fin (m + 1)) (xs : List (Fin (m + n))) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k xs).getLast? = xs.getLast?.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_getLast?, List.getLast?_map]

/-- 概要：一行から復元した外側選択語は非重複（BF §1.5.8）。
方針：元の可用外側逆置換行の先頭部分との一致を使う。
規約：元の選択長の正値性や上限は不要。
使われ方：水平境界の非一致から二行連結の非退化性を得る。 -/
lemma outerSelection_nodup {m n : ℕ} (k : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n))
    (removed : List (Fin (m + n))) (r : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
      (List.ofFn (permutationComposition m n k σ τ).symm)).take r)).Nodup := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerSelection_take k σ τ removed r
  rw [← h]
  exact ((List.nodup_ofFn_ofInjective σ.symm.injective).filter _).take

/-- 概要：非退化成功の水平二行の外側選択語の連結は非退化（BF §1.5.8）。
方針：両選択語内部は非重複性、境界は固定内側置換の外側境界非一致を使う。
規約：外側置換と除外状態と後続 table は任意。
使われ方：外側重複行を圧縮した全表の出力の非退化性を構成する。 -/
lemma horizontal_outer_selections_isChain {m n : ℕ} (k : Fin (m + 1))
    (σ σ' : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n))
    (removed out : List (Fin (m + n))) (r s : ℕ)
    (rest : List (List (Fin (m + n)) × ℕ))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
      ((List.ofFn (permutationComposition m n k σ τ).symm, r) ::
        (List.ofFn (permutationComposition m n k σ' τ).symm, s) :: rest)
      removed = some out) (hc : out.IsChain (· ≠ ·)) :
    let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm)
    let rem := removed ++ xs.take (r - 1)
    let ys := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available rem (List.ofFn (permutationComposition m n k σ' τ).symm)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k (xs.take r) ++ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k (ys.take s)).IsChain (· ≠ ·) := by
  obtain ⟨hr, hb, tail, ht, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
  obtain ⟨hs, hsb, _, _, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ ht
  let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm)
  let rem := removed ++ xs.take (r - 1)
  let ys := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available rem (List.ofFn (permutationComposition m n k σ' τ).symm)
  have hi : r - 1 < xs.length := by change r ≤ xs.length at hb; omega
  have hj : 0 < ys.length := by change s ≤ ys.length at hsb; omega
  let a := xs[r - 1]
  let b := ys[0]
  have he : xs[r - 1]? = some a := List.getElem?_eq_getElem hi
  have hh : ys.head? = some b := by
    rw [List.head?_eq_getElem?]
    exact List.getElem?_eq_getElem hj
  have hne := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_horizontal_outer_boundary_ne σ σ' τ k removed out
    r s rest a b he hh h hc
  have hlast : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k (xs.take r)).getLast? = some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k a) := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord_getLast?, List.getLast?_take, ite_eq_right (show r ≠ 0 by omega),
      he, Option.some_or, Option.map_some]
  have hhead : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k (ys.take s)).head? = some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k b) := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord_head?, List.head?_take, ite_eq_right (show s ≠ 0 by omega), hh,
      Option.map_some]
  apply (List.Pairwise.isChain (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerSelection_nodup k σ τ removed r)).append
    (List.Pairwise.isChain (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerSelection_nodup k σ' τ rem s))
  intro c hc d hd
  change c ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k (xs.take r)).getLast? at hc
  change d ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k (ys.take s)).head? at hd
  simp only [hlast, Option.mem_some_iff] at hc
  simp only [hhead, Option.mem_some_iff] at hd
  subst c
  subst d
  exact hne

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
