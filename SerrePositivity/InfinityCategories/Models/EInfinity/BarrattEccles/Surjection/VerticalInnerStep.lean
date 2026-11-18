module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.InnerRowProjection
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.VerticalBoundary
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapPrefix

/-!
模型。文献の定義との比較は後で
# 非退化な合成表から元の内側一行の抽出を復元

概要：Berger–Fresse §1.5.8 の垂直隣接行の前行を元の内側表の成功へ戻す。
方針：実際の行末が内側であることを成功と非退化性から導き、抽出証跡を射影する。
規約：除外状態は任意、射影行長は実際の選択語の内側射影の長さとする。
使われ方：垂直成分の全行を元の内側抽出へ戻す逆構成の一段。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

/-- 概要：垂直隣接行の前行の選択末尾は内側射影で残る（BF §1.5.8）。
方針：成功の行長条件で実際の末尾を取り出し、行末の内側性を適用する。
規約：抽出された take r 自体の getLast? で末尾を指定する。
使われ方：垂直先行部分の各選択行に射影証跡の条件を供給する。 -/
lemma permutationComposition_vertical_last_retained {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (τ τ' : Equiv.Perm (Fin n))
    (k : Fin (m + 1)) (removed out : List (Fin (m + n)))
    (r s : ℕ) (rest : List (List (Fin (m + n)) × ℕ))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
      ((List.ofFn (permutationComposition m n k σ τ).symm, r) ::
        (List.ofFn (permutationComposition m n k σ τ').symm, s) :: rest)
      removed = some out) (hc : out.IsChain (· ≠ ·)) :
    ∃ a b, ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
      (List.ofFn (permutationComposition m n k σ τ).symm)).take r).getLast? = some a ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k a = some b := by
  obtain ⟨hr, hb, _, _, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
  let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm)
  have hi : r - 1 < xs.length := by change r ≤ xs.length at hb; omega
  let a := xs[r - 1]
  have he : xs[r - 1]? = some a := List.getElem?_eq_getElem hi
  obtain ⟨b, ha⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_vertical_endpoint_inserted σ τ τ' k removed out a r s rest he h hc
  have hlast : (xs.take r).getLast? = some a := by
    rw [List.getLast?_take, ite_eq_right (show r ≠ 0 by omega), he, Option.some_or]
  exact ⟨a, b, hlast, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_eq_some_iff k a b).mpr ha⟩

/-- 概要：非退化成功の垂直隣接行の前行は内側一行の成功を与える（BF §1.5.8）。
方針：行末の内側性と部分単射による先行抽出の射影を組み合わせる。
規約：選択語と終端除外状態は実際の合成抽出の内側射影そのもの。
使われ方：任意の合成表から元の内側 table の行長と抽出成功を構成する。 -/
lemma permutationComposition_vertical_inner_step {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (τ τ' : Equiv.Perm (Fin n))
    (k : Fin (m + 1)) (removed out : List (Fin (m + n)))
    (r s : ℕ) (rest : List (List (Fin (m + n)) × ℕ))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
      ((List.ofFn (permutationComposition m n k σ τ).symm, r) ::
        (List.ofFn (permutationComposition m n k σ τ').symm, s) :: rest)
      removed = some out) (hc : out.IsChain (· ≠ ·)) :
    let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm)
    let picked := (xs.take r).filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix [(List.ofFn τ.symm, picked.length)]
      (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) [picked]
      ((removed ++ xs.take (r - 1)).filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) := by
  obtain ⟨hr, hb, _, _, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
  let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm)
  obtain ⟨a, b, hlast, ha⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_vertical_last_retained σ τ τ' k removed out r s rest h hc
  have ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix [(List.ofFn (permutationComposition m n k σ τ).symm, r)]
      removed [xs.take r] (removed ++ xs.take (r - 1)) := .cons hr hb (.nil _)
  have hp := ht.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_partial_injective k)
    (by
      intro word hw
      have hw' : word = xs.take r := List.mem_singleton.mp hw
      subst word
      exact ⟨a, b, hlast, ha⟩)
  simpa [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_permutationComposition_row, xs] using hp

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
