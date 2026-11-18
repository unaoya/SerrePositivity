module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapConsumption
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeInnerProjection
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.HorizontalRows
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.VerticalInnerFinal

/-!
模型。文献の定義との比較は後で
# 固定内側の水平区間を元の内側一行へ復元

概要：Berger–Fresse §1.5.8 の内側表の逆構成で、水平移動による同じ行の反復を融合する。
方針：実際の内側射影の全消費・末尾保持を集約し、最後の正の選択で通常の一行へ閉じる。
規約：水平区間は空でもよく、途中の内側選択は空でもよい。初期除外も任意。
使われ方：垂直成分間の接続と零歩成分から元の内側表全体を復元する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

/-- 概要：実際の水平抽出の内側射影は固定内側行の消費証跡を持つ（BF §1.5.8）。
方針：全ての合成逆置換行の内側射影が同じ行になることを部分単射射影へ渡す。
規約：外側置換・行長・初期状態は任意。内側選択の非空性は要求しない。
使われ方：外側末尾が捨てられる水平段も除外状態を正確に保持する。 -/
lemma horizontal_inner_consumption {m n : ℕ} (τ : Equiv.Perm (Fin n)) (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin (m + 1)) × ℕ))
    (removed finish : List (Fin (m + n))) (picked : List (List (Fin (m + n))))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows τ k entries) removed picked finish) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ConsumptionPrefix (List.ofFn τ.symm) (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k))
      (picked.flatten.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) (finish.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) := by
  apply h.filterMap_consumption (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_partial_injective k)
  intro p hp
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_permutationComposition_row k q.1 τ

/-- 概要：水平区間と非空な最終内側選択を元の内側一行へ戻す（BF §1.5.8）。
方針：全消費も許す先行射影を集約し、最後の射影選択の末尾を共有文字として残す。
規約：水平零歩も含む。最終合成末尾が外側なら内側末尾を復元終状態に戻す。
使われ方：零歩成分と垂直成分の間で元の内側抽出を接続する。 -/
lemma horizontal_inner_close {m n : ℕ} (τ : Equiv.Perm (Fin n)) (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin (m + 1)) × ℕ)) (σlast : Equiv.Perm (Fin (m + 1)))
    (s : ℕ) (removed finish : List (Fin (m + n))) (picked : List (List (Fin (m + n))))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows τ k entries) removed picked finish)
    (hne : List.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish (List.ofFn (permutationComposition m n k σlast τ).symm)).take s) ≠ []) :
    let last := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish (List.ofFn (permutationComposition m n k σlast τ).symm)).take s
    ∃ r : ℕ, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix [(List.ofFn τ.symm, r)] (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k))
      [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k (picked.flatten ++ last)]
      (finish.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) ++
        (last.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)).take ((last.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)).length - 1)) := by
  let last := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish (List.ofFn (permutationComposition m n k σlast τ).symm)).take s
  let inner := last.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)
  have hpick : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (finish.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) (List.ofFn τ.symm)).take
      inner.length = inner := by
    rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_available_composition_row k σlast τ finish, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMap_take_prefix]
  have hb : inner.length ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (finish.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k))
      (List.ofFn τ.symm)).length := by
    have hh := congrArg List.length hpick
    simp only [List.length_take] at hh
    omega
  have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontal_inner_consumption τ k entries removed finish picked h
  obtain ⟨r, hr⟩ := hp.close (List.nodup_ofFn_ofInjective τ.symm.injective) inner.length
    (List.length_pos_iff.mpr hne) hb
  have hshort : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (finish.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) (List.ofFn τ.symm)).take
      (inner.length - 1) = inner.take (inner.length - 1) := by
    have hh := congrArg (fun xs : List (Fin n) => xs.take (inner.length - 1)) hpick
    simpa only [List.take_take, Nat.min_eq_left (Nat.sub_le _ _)] using hh
  rw [hpick, hshort] at hr
  exact ⟨r, by simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord, List.filterMap_append] using hr⟩

/-- 概要：垂直移動直前までの全水平区間は元の内側一行を与える（BF §1.5.8）。
方針：最後の水平行の末尾保持を実際の垂直隣接成功から導き、先行消費と融合する。
規約：非空射影を追加仮定にせず、零歩の水平区間も実際の終状態へ接続する。
使われ方：成功 shuffle 表の内側各行を、水平移動を跨いで元の表へ戻す。 -/
lemma horizontal_inner_before_vertical {m n : ℕ}
    (τ τ' : Equiv.Perm (Fin n)) (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin (m + 1)) × ℕ)) (σlast : Equiv.Perm (Fin (m + 1)))
    (s t : ℕ) (removed finish tail : List (Fin (m + n)))
    (picked : List (List (Fin (m + n)))) (rest : List (List (Fin (m + n)) × ℕ))
    (hpre : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows τ k entries) removed picked finish)
    (hrest : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
      ((List.ofFn (permutationComposition m n k σlast τ).symm, s) ::
        (List.ofFn (permutationComposition m n k σlast τ').symm, t) :: rest)
      finish = some tail) (hc : tail.IsChain (· ≠ ·)) :
    let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish (List.ofFn (permutationComposition m n k σlast τ).symm)
    ∃ r : ℕ, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix [(List.ofFn τ.symm, r)] (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k))
      [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k (picked.flatten ++ xs.take s)]
      ((finish ++ xs.take (s - 1)).filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontal_inner_consumption τ k entries removed finish picked hpre
  have hq := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_vertical_inner_step σlast τ τ' k finish tail
    s t rest hrest hc
  obtain ⟨r, hr⟩ := hp.close_of_prefix (List.nodup_ofFn_ofInjective τ.symm.injective) _ hq
  exact ⟨r, by simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord, List.filterMap_append] using hr⟩

/-- 概要：最後の水平区間の非空な全内側射影は元の内側一行の成功を与える（BF §1.5.8）。
方針：全区間の消費証跡を集約し、通常の一行の抽出として閉じる。
規約：最後の行だけの内側非空性は要求せず、区間全体の内側非空性を使う。
使われ方：内側文字を選ばない末尾の水平行を捨てず、元の最終内側行へ戻す。 -/
lemma horizontal_inner_success {m n : ℕ} (τ : Equiv.Perm (Fin n)) (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin (m + 1)) × ℕ))
    (removed finish : List (Fin (m + n))) (picked : List (List (Fin (m + n))))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows τ k entries) removed picked finish)
    (hne : picked.flatten.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) ≠ []) :
    ∃ r : ℕ, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows [(List.ofFn τ.symm, r)] (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) =
      some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerWord k picked.flatten) := by
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontal_inner_consumption τ k entries removed finish picked h).reduction
    (List.nodup_ofFn_ofInjective τ.symm.injective) hne

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
