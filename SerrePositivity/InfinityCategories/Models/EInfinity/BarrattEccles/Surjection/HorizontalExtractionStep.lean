module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SubstitutionHeadPrefix
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.PermutationStateSubstitution
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SingletonRows

/-!
模型。文献の定義との比較は後で
# 最終除外前の水平行の実際の合成抽出

概要：Berger–Fresse §1.5.7 の外側選択行を固定した内側頂点で合成して抽出する。
方針：選択末尾以前に指定値がないことから内側先頭だけを使う先頭計算を適用する。
規約：内側の未選択文字は除外せず、同じ内側状態を保つ。
使われ方：外側の最終除外前の水平成分を一行ずつ転送する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：指定値を末尾以前に除外しない水平行の合成抽出成功（BF §1.5.7）。
方針：選択語と末尾以外の選択を水平ラベル写像で移し、同じ内側状態の後続へ接続する。
規約：選択末尾の指定値は内側先頭の一文字に移す。
使われ方：元の外側の成功証跡を水平ブロックへ帰納的に移す一段。 -/
lemma horizontalExtractionStep_success {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n)) (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner : List (Fin n)) (b : Fin n) (ys : List (Fin n))
    (hinner : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available inner (List.ofFn τ.symm) = b :: ys) (r : ℕ) (hr : 0 < r)
    (hb : r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available outer (List.ofFn σ.symm)).length)
    (hk : k ∉ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available outer (List.ofFn σ.symm)).take (r - 1))
    (rest : List (List (Fin (m + n)) × ℕ)) (tail : List (Fin (m + n)))
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k
      (outer ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available outer (List.ofFn σ.symm)).take (r - 1)) inner) = some tail) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((List.ofFn (permutationComposition m n k σ τ).symm, r) :: rest)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) =
      some (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available outer (List.ofFn σ.symm)).take r).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b) ++ tail) := by
  let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available outer (List.ofFn σ.symm)
  let row := List.ofFn (permutationComposition m n k σ τ).symm
  have hbs : r ≤ xs.length := hb
  have hks : k ∉ xs.take (r - 1) := hk
  have hrow : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) row =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs [b :: ys] := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_state_available_substitute, hinner]
  have htake : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) row).take r =
      (xs.take r).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b) := by
    rw [hrow]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_head_prefix k b ys xs r hbs hks
  have hlen : r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) row).length := by
    have hl := congrArg List.length htake
    simp only [List.length_take, List.length_map, Nat.min_eq_left hbs] at hl
    omega
  have hremoved : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) row).take (r - 1) =
      (xs.take (r - 1)).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b) := by
    rw [hrow]
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_head_prefix k b ys xs (r - 1) (by omega)
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.not_mem_take_of_le xs k (by omega) hks
  have hup : ∀ x, x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) row).take (r - 1) ↔
      x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k (outer ++ xs.take (r - 1)) inner := by
    intro x
    rw [hremoved]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel_state_update k b outer inner _ hks x
  have ht' := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_congr_removed rest _ _ hup).trans ht
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success row r rest _ tail hr hlen ht'
  simpa only [htake] using hs

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
