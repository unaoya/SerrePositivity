module

public import SerrePositivity.EInfinity.Surjection.CompositionStateAvailable
public import SerrePositivity.EInfinity.Surjection.PermutationAvailableSubstitution

/-!
# 全段階の合成除外状態と実際の利用可能行

概要：Berger–Fresse §1.5.7 の行の式を外側指定値の最終除外後も含めて証明する。
方針：指定値が未除外なら既存の式、除外済みなら内側ブロックの消滅を使う。
規約：元の二つの除外リストは任意。
使われ方：経路上の合成表で用いる全段階の状態不変条件。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection

open BarrattEccles TableReduction

/-- 概要：全段階で利用可能な合成行は元の利用可能行への代入（BF §1.5.7）。
方針：指定値の除外前後で分け、除外後は内側が消えた二つの外側部分を照合する。
規約：未除外の指定値という追加仮定を要求しない。
使われ方：元の二表から合成表の抽出を作る行ごとの不変条件。 -/
lemma permutationComposition_state_available_substitute {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n)) (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner : List (Fin n)) :
    available (compositionStateRemoved k outer inner)
        (List.ofFn (permutationComposition m n k σ τ).symm) =
      substitute k (available outer (List.ofFn σ.symm))
        [available inner (List.ofFn τ.symm)] := by
  by_cases hk : k ∈ outer
  · rw [permutationComposition_inverse_row, permutationCompositeRow]
    conv_lhs => simp only [available, List.filter_append]
    change available (compositionStateRemoved k outer inner)
        ((permutationBefore σ k).map (remainingPosition m n k)) ++
      (available (compositionStateRemoved k outer inner)
        ((List.ofFn τ.symm).map (insertedPosition m n k)) ++
      available (compositionStateRemoved k outer inner)
        ((permutationAfter σ k).map (remainingPosition m n k))) =
        substitute k (available outer (List.ofFn σ.symm))
          [available inner (List.ofFn τ.symm)]
    rw [available_state_remaining_block, available_state_inserted_of_mem k outer _ _ hk,
      available_state_remaining_block, List.nil_append, permutation_inverse_row_split σ k]
    have hout : available outer
        ((permutationBefore σ k).map Subtype.val ++ k ::
          (permutationAfter σ k).map Subtype.val) =
        ((permutationBefore σ k).filter (fun a => a.val ∉ outer)).map Subtype.val ++
          ((permutationAfter σ k).filter (fun a => a.val ∉ outer)).map Subtype.val := by
      simp only [available, List.filter_append, List.filter_cons, decide_eq_false (not_not.mpr hk),
        Bool.false_eq_true, ite_false,
        List.filter_map, Function.comp_def]
    rw [hout, substitute_remaining_prefix, substitute_remaining_word]
  · rw [compositionStateRemoved_of_not_mem k outer inner hk]
    exact permutationComposition_available_substitute σ τ k outer inner hk

end SerrePositivity.EInfinity.Surjection
