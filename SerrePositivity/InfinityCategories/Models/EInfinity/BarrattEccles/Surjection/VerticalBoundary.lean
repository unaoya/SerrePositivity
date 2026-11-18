module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.PermutationCompositeRow
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.BlockBoundaryHead

/-!
模型。文献の定義との比較は後で
# 固定した外側置換の連続合成行の末尾

概要：Berger–Fresse §1.5.8 の非退化な合成 table の垂直行末制約を証明する。
方針：実際の逆合成置換行を三ブロックへ分け、中央以外での切断を排除する。
規約：外側置換を固定し、内側置換・除外状態・後続 table は任意。
使われ方：合成 table の逆構成で内側の行長と元の抽出を復元する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：内側逆置換の行は並び順によらず同じ挿入ラベル集合を持つ（BF §1.5.8）。
方針：任意の内側値 b は逆置換の位置 τ(b) に現れる。
規約：空の内側 arity も含む。
使われ方：合成行の中央ブロックの所属集合を一致させる。 -/
lemma inserted_permutation_row_mem_iff {m n : ℕ} (k : Fin (m + 1))
    (τ τ' : Equiv.Perm (Fin n)) (a : Fin (m + n)) :
    a ∈ (List.ofFn τ'.symm).map (insertedPosition m n k) ↔
      a ∈ (List.ofFn τ.symm).map (insertedPosition m n k) := by
  constructor
  · rintro ha
    obtain ⟨b, _, hb⟩ := List.mem_map.mp ha
    exact List.mem_map.mpr ⟨b, List.mem_ofFn.mpr ⟨τ b, τ.symm_apply_apply b⟩, hb⟩
  · rintro ha
    obtain ⟨b, _, hb⟩ := List.mem_map.mp ha
    exact List.mem_map.mpr ⟨b, List.mem_ofFn.mpr ⟨τ' b, τ'.symm_apply_apply b⟩, hb⟩

/-- 概要：非退化な成功 table の垂直隣接行の前行末は挿入ラベル（BF §1.5.8）。
方針：実際の逆置換行を三ブロック表示へ移し、外側末尾の境界重複を使う。
規約：前行末は除外前の可用行の r−1 番目。後続全体の成功を仮定する。
使われ方：任意の非退化な成功合成 table から元の内側抽出を復元する。 -/
lemma permutationComposition_vertical_endpoint_inserted {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (τ τ' : Equiv.Perm (Fin n))
    (k : Fin (m + 1)) (removed out : List (Fin (m + n)))
    (a : Fin (m + n)) (r s : ℕ) (rest : List (List (Fin (m + n)) × ℕ))
    (he : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
      (List.ofFn (permutationComposition m n k σ τ).symm))[r - 1]? = some a)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
      ((List.ofFn (permutationComposition m n k σ τ).symm, r) ::
        (List.ofFn (permutationComposition m n k σ τ').symm, s) :: rest)
      removed = some out) (hc : out.IsChain (· ≠ ·)) :
    ∃ b : Fin n, a = insertedPosition m n k b := by
  have hn := List.nodup_ofFn_ofInjective
    (permutationComposition m n k σ τ).symm.injective
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_inverse_row, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow,
    ← List.append_assoc] at he h hn
  have hm := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_block_endpoint_mem_middle
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore σ k).map (remainingPosition m n k))
    ((List.ofFn τ.symm).map (insertedPosition m n k))
    ((List.ofFn τ'.symm).map (insertedPosition m n k))
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter σ k).map (remainingPosition m n k))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.inserted_permutation_row_mem_iff k τ τ') hn removed out a r s rest he h hc
  obtain ⟨b, _, hb⟩ := List.mem_map.mp hm
  exact ⟨b, hb.symm⟩

/-- 概要：非退化な成功 table の垂直隣接行の次行先頭も挿入ラベル（BF §1.5.8）。
方針：前行末が内側にあることから外側前半の全除外と内側の非空性を得る。
規約：次行先頭は実際の除外更新後の可用行で評価する。
使われ方：垂直連続成分の内側部分を一つの元の table へ戻す。 -/
lemma permutationComposition_vertical_next_head_inserted {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (τ τ' : Equiv.Perm (Fin n))
    (k : Fin (m + 1)) (removed out : List (Fin (m + n)))
    (a b : Fin (m + n)) (r s : ℕ) (rest : List (List (Fin (m + n)) × ℕ))
    (he : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
      (List.ofFn (permutationComposition m n k σ τ).symm))[r - 1]? = some a)
    (hb : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
      (List.ofFn (permutationComposition m n k σ τ).symm)).take (r - 1))
      (List.ofFn (permutationComposition m n k σ τ').symm)).head? = some b)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
      ((List.ofFn (permutationComposition m n k σ τ).symm, r) ::
        (List.ofFn (permutationComposition m n k σ τ').symm, s) :: rest)
      removed = some out) (hc : out.IsChain (· ≠ ·)) :
    ∃ c : Fin n, b = insertedPosition m n k c := by
  obtain ⟨a', ha'⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_vertical_endpoint_inserted σ τ τ' k removed out a r s rest he h hc
  have ha : a ∈ (List.ofFn τ.symm).map (insertedPosition m n k) :=
    List.mem_map.mpr ⟨a', List.mem_ofFn.mpr ⟨τ a', τ.symm_apply_apply a'⟩, ha'.symm⟩
  have hr := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h).1
  have hn := List.nodup_ofFn_ofInjective
    (permutationComposition m n k σ τ).symm.injective
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_inverse_row, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow,
    ← List.append_assoc] at he hb hn
  have hm := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_block_next_head_mem_middle
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore σ k).map (remainingPosition m n k))
    ((List.ofFn τ.symm).map (insertedPosition m n k))
    ((List.ofFn τ'.symm).map (insertedPosition m n k))
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter σ k).map (remainingPosition m n k))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.inserted_permutation_row_mem_iff k τ τ') hn removed a b r hr he ha hb
  obtain ⟨c, _, hc⟩ := List.mem_map.mp hm
  exact ⟨c, hc.symm⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
