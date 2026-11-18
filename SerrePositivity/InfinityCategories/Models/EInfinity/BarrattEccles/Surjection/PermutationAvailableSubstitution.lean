module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionAvailable
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.PermutationRowSubstitution

/-!
模型。文献の定義との比較は後で
# 利用可能な合成置換行と一出現の代入

概要：Berger–Fresse §1.5.7 の合成 table の一行で除外処理と代入を照合する。
方針：逆置換行の三ブロック表示に内外のフィルターを適用する。
規約：外側の指定値はまだ除外されていない。
使われ方：shuffle 経路上の合成表の成功抽出を構成する一段の式。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：未除外の指定値で元の利用可能な逆置換行を分ける（BF §1.5.7）。
方針：逆置換行の前後分割を外側の除外でフィルターする。
規約：前後の部分は指定値以外の部分型を保持する。
使われ方：合成行の代入表示を具体的な三つの利用可能ブロックに直す。 -/
lemma available_permutation_inverse_row_split {m : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (hk : k ∉ outer) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available outer (List.ofFn σ.symm) =
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore σ k).filter (fun a => a.val ∉ outer)).map Subtype.val ++
        k :: ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter σ k).filter (fun a => a.val ∉ outer)).map Subtype.val := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutation_inverse_row_split σ k]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.filter_append, List.filter_cons, decide_eq_true hk, ite_true,
    List.filter_map, Function.comp_def]

/-- 概要：利用可能な合成行は元の利用可能行への代入（BF §1.5.7）。
方針：内外の除外所属で三ブロックを別々にフィルターし、一出現代入を評価する。
規約：指定値 k が外側の除外リストに含まれないことだけを要求する。
使われ方：二つの table の抽出状態から合成 table の抽出状態を進める。 -/
lemma permutationComposition_available_substitute {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n)) (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner : List (Fin n)) (hk : k ∉ outer) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionRemoved k outer inner)
        (List.ofFn (permutationComposition m n k σ τ).symm) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available outer (List.ofFn σ.symm))
        [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available inner (List.ofFn τ.symm)] := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_inverse_row, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow]
  conv_lhs => simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.filter_append]
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionRemoved k outer inner)
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore σ k).map (remainingPosition m n k)) ++
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionRemoved k outer inner)
      ((List.ofFn τ.symm).map (insertedPosition m n k)) ++
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionRemoved k outer inner)
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter σ k).map (remainingPosition m n k))) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available outer (List.ofFn σ.symm))
        [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available inner (List.ofFn τ.symm)]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.available_remaining_block, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.available_inserted_block, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.available_remaining_block,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.available_permutation_inverse_row_split σ k outer hk, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_one_slot]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
