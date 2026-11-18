module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.InnerWordBoundary
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.VerticalInnerFinal

/-!
模型。文献の定義との比較は後で
# 実際の垂直移動で内側復元語を接続

概要：Berger–Fresse §1.5.8 の水平区間間の垂直辺で、復元語の連結と後続非空性を得る。
方針：元の成功から残る両端を取り、非退化な境界と部分単射性で内側語を分離する。
規約：先行区間の語は任意。次の区間の内側非空性を仮定しない。
使われ方：実際の全合成表から元の内側表を帰納的に復元する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：実際の非退化な垂直成功は内側語の接続と後続射影の非空性を与える（BF §1.5.8）。
方針：前行末と次行先頭の挿入ラベルを成功から導き、復元語の分離連結を使う。
規約：tail は前行を除いた実際の出力。先行語 pre の内部に条件を課さない。
使われ方：水平区間の一行を後続の復元表へ接続し、その帰納の非空性も供給する。 -/
lemma vertical_inner_join {m n : ℕ} (k : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ τ' : Equiv.Perm (Fin n))
    (r s : ℕ) (rest : List (List (Fin (m + n)) × ℕ))
    (removed pre tail : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
      ((List.ofFn (permutationComposition m n k σ τ).symm, r) ::
        (List.ofFn (permutationComposition m n k σ τ').symm, s) :: rest)
      removed = some ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
        (List.ofFn (permutationComposition m n k σ τ).symm)).take r ++ tail))
    (hc : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm)).take r ++
      tail).IsChain (· ≠ ·)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k (pre ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
      (List.ofFn (permutationComposition m n k σ τ).symm)).take r ++ tail) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k (pre ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
          (List.ofFn (permutationComposition m n k σ τ).symm)).take r) ++ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k tail ∧
      tail.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) ≠ [] := by
  obtain ⟨hr, hb, actualTail, ht, ho⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
  have heq : tail = actualTail := List.append_cancel_left ho
  subst actualTail
  let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm)
  let rem := removed ++ xs.take (r - 1)
  let ys := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available rem (List.ofFn (permutationComposition m n k σ τ').symm)
  obtain ⟨hs, hsb, post, hpost, htail⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ ht
  obtain ⟨a, a', hlast, hfa⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_vertical_last_retained σ τ τ' k
    removed _ r s rest h hc
  have he : xs[r - 1]? = some a := by
    rw [List.getLast?_take, ite_eq_right (show r ≠ 0 by omega)] at hlast
    change (xs[r - 1]?.or xs.getLast?) = some a at hlast
    have hi : r - 1 < xs.length := by change r ≤ xs.length at hb; omega
    rw [List.getElem?_eq_getElem hi, Option.some_or] at hlast
    exact (List.getElem?_eq_getElem hi).trans hlast
  have hi : 0 < ys.length := by change s ≤ ys.length at hsb; omega
  let b := ys[0]
  have hh : ys.head? = some b := by
    rw [List.head?_eq_getElem?]
    exact List.getElem?_eq_getElem hi
  obtain ⟨b', hbb⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_vertical_next_head_inserted σ τ τ' k
    removed _ a b r s rest he hh h hc
  have hfb : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k b = some b' := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_eq_some_iff k b b').mpr hbb
  have hhTail : tail.head? = some b := by
    rw [htail, List.head?_append, List.head?_take, ite_eq_right (show s ≠ 0 by omega)]
    change (ys.head?.or post.head?) = some b
    rw [hh, Option.some_or]
  have hne : a ≠ b := (List.isChain_append.mp hc).2.2 a
    (by simpa only [hlast] using (show a ∈ (some a : Option (Fin (m + n))) from rfl)) b
    (by simpa only [hhTail] using (show b ∈ (some b : Option (Fin (m + n))) from rfl))
  have hlastPre : (pre ++ xs.take r).getLast? = some a := by
    rw [List.getLast?_append, hlast, Option.some_or]
  refine ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord_append_of_retained k (pre ++ xs.take r) tail a b a' b'
    hlastPre hhTail hfa hfb hne, ?_⟩
  obtain ⟨post', hp⟩ := List.head?_eq_some_iff.mp hhTail
  rw [hp, List.filterMap_cons, hfb]
  exact List.cons_ne_nil _ _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
