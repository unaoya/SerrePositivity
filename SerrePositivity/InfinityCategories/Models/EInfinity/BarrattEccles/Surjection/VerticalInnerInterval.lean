module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.VerticalInnerFinal
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.VerticalInnerPrefix

/-!
模型。文献の定義との比較は後で
# 垂直成分全体を内側の抽出区間へ復元

概要：Berger–Fresse §1.5.8 の少なくとも一歩を持つ垂直成分の全行を射影する。
方針：先行行の終状態を保って射影し、最終行は内側末尾を残す形で接続する。
規約：最終行の内側非空性は直前の垂直行と全出力の非退化性から導く。
使われ方：合成 table の逆構成で、各垂直成分から元の内側 table の区間を作る。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

/-- 概要：非自明な垂直成分の最終選択語の内側射影は非空（BF §1.5.8）。
方針：先行行を帰納的に剥がし、最後の二行の実際の成功に内側先頭制約を使う。
規約：最終行以降の後続 table は任意。先行部分が一行以上あることを要求する。
使われ方：最終行の内側抽出の正の行長を元の成功だけから得る。 -/
lemma vertical_interval_final_inner_nonempty {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin n) × ℕ)) (τlast : Equiv.Perm (Fin n))
    (s : ℕ) (rest : List (List (Fin (m + n)) × ℕ))
    (removed finish tail : List (Fin (m + n))) (picked : List (List (Fin (m + n))))
    (hpre : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.verticalTable σ k entries) removed picked finish)
    (hrest : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((List.ofFn (permutationComposition m n k σ τlast).symm, s) :: rest)
      finish = some tail) (hc : (picked.flatten ++ tail).IsChain (· ≠ ·))
    (hne : entries ≠ []) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish (List.ofFn (permutationComposition m n k σ τlast).symm)).take s).filterMap
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) ≠ [] := by
  induction entries generalizing removed picked with
  | nil => exact (hne rfl).elim
  | cons entry entries ih =>
    obtain ⟨τ, r⟩ := entry
    have hfull := hpre.append
      ((List.ofFn (permutationComposition m n k σ τlast).symm, s) :: rest) tail hrest
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix
      ((List.ofFn (permutationComposition m n k σ τ).symm, r) :: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.verticalTable σ k entries)
      removed picked finish at hpre
    cases hpre with
    | @cons _ _ _ _ picked _ hr hb ht =>
      have hc' : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
          (List.ofFn (permutationComposition m n k σ τ).symm)).take r ++
          (picked.flatten ++ tail)).IsChain (· ≠ ·) := by
        simpa only [List.flatten_cons, List.append_assoc] using hc
      cases entries with
      | nil =>
        cases ht
        exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_vertical_next_inner_nonempty σ τ τlast k removed _
          r s rest (by simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.verticalTable, List.map_cons, List.map_nil,
            List.cons_append, List.nil_append] using hfull) hc
      | cons entry entries =>
        exact ih _ _ ht hc'.right_of_append (by simp)

/-- 概要：非自明な垂直成分の全選択語を元の内側区間として抽出できる（BF §1.5.8）。
方針：非最終先行部分の射影に、非空な内側最終選択語の抽出を接続する。
規約：最後の内側文字は除外せず、後続成分との共有端点として保持する。
使われ方：任意の成功経路表から元の成功内側表を逆構成する成分。 -/
lemma vertical_interval_inner_projection {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin n) × ℕ)) (τlast : Equiv.Perm (Fin n))
    (s : ℕ) (rest : List (List (Fin (m + n)) × ℕ))
    (removed finish tail : List (Fin (m + n))) (picked : List (List (Fin (m + n))))
    (hpre : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.verticalTable σ k entries) removed picked finish)
    (hrest : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((List.ofFn (permutationComposition m n k σ τlast).symm, s) :: rest)
      finish = some tail) (hc : (picked.flatten ++ tail).IsChain (· ≠ ·))
    (hne : entries ≠ []) :
    let last := ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish
      (List.ofFn (permutationComposition m n k σ τlast).symm)).take s).filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.verticalTable σ k entries) picked ++
        [(List.ofFn τlast.symm, last.length)])
      (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) (picked.map (List.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) ++ [last])
      (finish.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) ++ last.take (last.length - 1)) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.vertical_prefix_inner_projection σ k entries τlast s rest removed finish tail
    picked hpre hrest hc
  have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.vertical_interval_final_inner_nonempty σ k entries τlast s rest removed finish
    tail picked hpre hrest hc hne
  have hq := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_inner_final_step σ τlast k finish s hn
  exact hp.trans hq

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
