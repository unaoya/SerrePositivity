module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.PermutationRowPieces
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.BlockCoordinates

/-!
模型。文献の定義との比較は後で
# 合成置換の逆置換行の三ブロック表示

概要：Berger–Fresse §1.5.7 の合成 table の一行を外側前半・内側行・外側後半へ分解する。
方針：各ブロックの文字に合成置換を作用させ、元の位置へ戻ることを確認する。
規約：空の内側行も含む。
使われ方：除外集合でフィルターした合成行を二つの元の行から構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：逆置換の外側前半・内側行・外側後半を連結した合成行（BF §1.5.7）。
方針：外側の残りラベルと内側挿入ラベルを既存の同値で移す。
規約：内側が空なら二つの外側部分だけを連結する。
使われ方：実際の置換合成の逆置換行の明示式。 -/
def permutationCompositeRow {m n : ℕ} (σ : Equiv.Perm (Fin (m + 1)))
    (τ : Equiv.Perm (Fin n)) (k : Fin (m + 1)) : List (Fin (m + n)) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore σ k).map (remainingPosition m n k) ++
    ((List.ofFn τ.symm).map (insertedPosition m n k) ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter σ k).map (remainingPosition m n k))

/-- 概要：合成行の長さは合成 arity（BF §1.5.7）。
方針：三つのブロック長を足す。
規約：内側 arity 零も含む。
使われ方：逆置換の一行表示と各位置で比較する。 -/
@[simp] lemma permutationCompositeRow_length {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n)) (k : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow σ τ k).length = m + n := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow, List.length_append, List.length_map,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore_length, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter_length, List.length_ofFn]
  have := (σ k).isLt
  omega

/-- 概要：合成行の各文字に合成置換を作用させるとその位置へ戻る（BF §1.5.7）。
方針：三ブロックに分け、既存の内外ラベルの作用公式を適用する。
規約：出力位置は実際の連結行の有限添字。
使われ方：逆置換行との一致を一意性で示す。 -/
lemma permutationCompositeRow_apply {m n : ℕ} (σ : Equiv.Perm (Fin (m + 1)))
    (τ : Equiv.Perm (Fin n)) (k : Fin (m + 1))
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow σ τ k).length) :
    (permutationComposition m n k σ τ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow σ τ k)[j.val])).val = j.val := by
  by_cases hb : j.val < (σ k).val
  · have hlen : j.val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore σ k).length := by simpa using hb
    have hv : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow σ τ k)[j.val] =
        remainingPosition m n k ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore σ k)[j.val]) := by
      have hb' : j.val < ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore σ k).map (remainingPosition m n k)).length := by
        simpa only [List.length_map] using hlen
      have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.getElem_of_block_position (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow σ τ k) []
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore σ k).map (remainingPosition m n k))
        ((List.ofFn τ.symm).map (insertedPosition m n k) ++
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter σ k).map (remainingPosition m n k)) rfl j ⟨j.val, hb'⟩
          (by simp)
      simpa only [List.getElem_map] using h
    rw [hv, permutationComposition_remaining_val,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore_get_apply σ k ⟨j.val, hlen⟩, remainingValue, ite_eq_left hb]
  · by_cases hi : j.val < (σ k).val + n
    · have hidx : j.val - (σ k).val < n := by omega
      have hv : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow σ τ k)[j.val] =
          insertedPosition m n k (τ.symm ⟨j.val - (σ k).val, hidx⟩) := by
        have hlen : j.val - (σ k).val <
            ((List.ofFn τ.symm).map (insertedPosition m n k)).length := by
          simpa only [List.length_map, List.length_ofFn] using hidx
        have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.getElem_of_block_position (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow σ τ k)
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore σ k).map (remainingPosition m n k))
          ((List.ofFn τ.symm).map (insertedPosition m n k))
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter σ k).map (remainingPosition m n k)) rfl j
          ⟨j.val - (σ k).val, hlen⟩ (by
            simp only [List.length_map, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore_length]
            omega)
        simpa only [List.getElem_map, List.getElem_ofFn] using h
      rw [hv, permutationComposition_inside, insertedPosition_val, τ.apply_symm_apply]
      change (σ k).val + (j.val - (σ k).val) = j.val
      omega
    · have hidx : j.val - (σ k).val - n < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter σ k).length := by
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter_length]
        have hj := j.isLt
        have hlen := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow_length σ τ k
        have := (σ k).isLt
        omega
      have hv : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow σ τ k)[j.val] = remainingPosition m n k
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter σ k)[j.val - (σ k).val - n]) := by
        have hlen : j.val - (σ k).val - n <
            ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter σ k).map (remainingPosition m n k)).length := by
          simpa only [List.length_map] using hidx
        have he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow σ τ k =
            (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore σ k).map (remainingPosition m n k) ++
              (List.ofFn τ.symm).map (insertedPosition m n k)) ++
                (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter σ k).map (remainingPosition m n k)) ++ [] := by
          simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow, List.append_nil, List.append_assoc]
        have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.getElem_of_block_position (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow σ τ k)
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore σ k).map (remainingPosition m n k) ++
            (List.ofFn τ.symm).map (insertedPosition m n k))
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter σ k).map (remainingPosition m n k)) []
          (by simpa only [List.append_assoc, List.append_nil] using he) j
          ⟨j.val - (σ k).val - n, hlen⟩ (by
            simp only [List.length_append, List.length_map, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore_length,
              List.length_ofFn]
            omega)
        simpa only [List.getElem_map] using h
      rw [hv, permutationComposition_remaining_val,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter_get_apply σ k ⟨j.val - (σ k).val - n, hidx⟩, remainingValue,
        ite_eq_right (by omega)]
      change (σ k).val + 1 + (j.val - (σ k).val - n) + n - 1 = j.val
      omega

/-- 概要：実際の合成置換の逆置換行は三つのブロックの連結（BF §1.5.7）。
方針：全長と各位置の値を合成置換の単射性で比較する。
規約：零 arity の挿入も含む。
使われ方：合成 table の一行の抽出を元の二つの行から組み立てる。 -/
lemma permutationComposition_inverse_row {m n : ℕ} (σ : Equiv.Perm (Fin (m + 1)))
    (τ : Equiv.Perm (Fin n)) (k : Fin (m + 1)) :
    List.ofFn (permutationComposition m n k σ τ).symm = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow σ τ k := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow_length]
  · intro i hi hj
    rw [List.getElem_ofFn]
    apply (permutationComposition m n k σ τ).injective
    exact ((permutationComposition m n k σ τ).apply_symm_apply _).trans
      (Fin.ext (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow_apply σ τ k ⟨i, hj⟩).symm)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
