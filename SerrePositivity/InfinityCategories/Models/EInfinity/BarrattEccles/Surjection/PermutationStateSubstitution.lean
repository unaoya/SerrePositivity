module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionStateAvailable
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.PermutationAvailableSubstitution

/-!
模型。文献の定義との比較は後で
# 全段階の合成除外状態と実際の利用可能行

概要：Berger–Fresse §1.5.7 の行の式を外側指定値の最終除外後も含めて証明する。
方針：指定値が未除外なら既存の式、除外済みなら内側ブロックの消滅を使う。
規約：元の二つの除外リストは任意。
使われ方：経路上の合成表で用いる全段階の状態不変条件。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：全段階で利用可能な合成行は元の利用可能行への代入（BF §1.5.7）。
方針：指定値の除外前後で分け、除外後は内側が消えた二つの外側部分を照合する。
規約：未除外の指定値という追加仮定を要求しない。
使われ方：元の二表から合成表の抽出を作る行ごとの不変条件。 -/
lemma permutationComposition_state_available_substitute {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n)) (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner : List (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner)
        (List.ofFn (permutationComposition m n k σ τ).symm) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available outer (List.ofFn σ.symm))
        [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available inner (List.ofFn τ.symm)] := by
  by_cases hk : k ∈ outer
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_inverse_row, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow]
    conv_lhs => simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.filter_append]
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner)
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore σ k).map (remainingPosition m n k)) ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner)
        ((List.ofFn τ.symm).map (insertedPosition m n k)) ++
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner)
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter σ k).map (remainingPosition m n k))) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available outer (List.ofFn σ.symm))
          [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available inner (List.ofFn τ.symm)]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.available_state_remaining_block, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.available_state_inserted_of_mem k outer _ _ hk,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.available_state_remaining_block, List.nil_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutation_inverse_row_split σ k]
    have hout : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available outer
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore σ k).map Subtype.val ++ k ::
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter σ k).map Subtype.val) =
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore σ k).filter (fun a => a.val ∉ outer)).map Subtype.val ++
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter σ k).filter (fun a => a.val ∉ outer)).map Subtype.val := by
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.filter_append, List.filter_cons, decide_eq_false (not_not.mpr hk),
        Bool.false_eq_true, ite_false,
        List.filter_map, Function.comp_def]
    rw [hout, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_remaining_prefix, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_remaining_word]
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved_of_not_mem k outer inner hk]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_available_substitute σ τ k outer inner hk

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
