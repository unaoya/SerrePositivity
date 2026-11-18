module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompressedOuterRecovery
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.HorizontalOuterSelections
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CompressionNondegenerate
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SpecifiedRowTrace

/-!
模型。文献の定義との比較は後で
# 水平・垂直に進む合成表の圧縮外側語の非退化性

概要：Berger–Fresse §1.5.8 の格子経路表で、復元外側選択語を実際の抽出証跡へ移す。
方針：行長と出力の一致で証跡を固定し、水平境界を圧縮後の非退化性へ反映する。
規約：隣接する行では外側か内側の少なくとも一方の置換を固定する。
使われ方：元の外側非退化全射語と成功 Schedule を逆構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：外側復元表の行長は指定した外側復元語の各長さ（BF §1.5.8）。
方針：行と選択語の長さ一致により zipWith が全行を対応させる。
規約：行数一致だけを要求し、成功はこの計算自体には不要。
使われ方：平坦な成功を指定行分割の抽出証跡へ戻す。 -/
lemma recoveredOuterTable_lengths {m n : ℕ} (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ))
    (picked : List (List (Fin (m + n)))) (hl : entries.length = picked.length) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable k entries picked).map Prod.snd =
      (picked.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k)).map List.length := by
  induction entries generalizing picked with
  | nil => cases picked <;> simp_all [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable]
  | cons entry entries ih =>
    cases picked with
    | nil => simp only [List.length_cons, List.length_nil] at hl; omega
    | cons word picked =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable, List.zipWith_cons_cons, List.map_cons]
      exact congrArg ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k word).length :: ·) (ih picked hl)

/-- 概要：外側復元の各選択語は元の外側抽出の実際の選択行（BF §1.5.8）。
方針：全外側成功と指定した行長を合わせ、行分割の一意性を適用する。
規約：元の先行部分の全選択語と初期の復元状態をそのまま保持する。
使われ方：実際の外側抽出証跡へ水平境界の非一致を渡す。 -/
lemma recoveredOuterTable_trace {m n : ℕ} (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ))
    (removed finish : List (Fin (m + n))) (picked : List (List (Fin (m + n))))
    (hpre : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k entries) removed picked finish) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable k entries picked) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed)
      (picked.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k)) := by
  have hl : entries.length = picked.length := by
    simpa only [List.length_map, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable] using
      (congrArg List.length hpre.lengths).symm
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionTrace_of_lengths
  · simpa only [List.append_nil] using
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outer_prefix_success k entries removed finish picked hpre [] [] rfl
  · exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable_lengths k entries picked hl).symm

/-- 概要：格子方向だけに動く非退化な成功表の外側復元は異なる行の境界が非退化（BF §1.5.8）。
方針：外側が変わる境界では内側が固定されることから水平二語の非退化性を使う。
規約：外側が同じ境界は融合するため制約しない。
使われ方：復元した外側抽出の圧縮後の全出力を非退化にする。 -/
lemma recoveredOuterTable_separated {m n : ℕ} (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ))
    (removed finish : List (Fin (m + n))) (picked : List (List (Fin (m + n))))
    (hpre : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k entries) removed picked finish)
    (hc : picked.flatten.IsChain (· ≠ ·))
    (haxis : entries.IsChain (fun p q => p.1 = q.1 ∨ p.2.1 = q.2.1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedBoundaries (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable k entries picked) (picked.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k)) := by
  induction entries generalizing removed picked with
  | nil => cases hpre; trivial
  | cons entry entries ih =>
    obtain ⟨σ, τ, r⟩ := entry
    have hfull := hpre.append [] [] rfl
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix
      ((List.ofFn (permutationComposition m n k σ τ).symm, r) :: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k entries)
      removed picked finish at hpre
    cases hpre with
    | @cons _ _ _ _ picked _ hr hb ht =>
      have hcTail : picked.flatten.IsChain (· ≠ ·) := by
        rw [List.flatten_cons] at hc
        exact hc.right_of_append
      have htail := ih _ _ ht hcTail haxis.tail
      cases entries with
      | nil => trivial
      | cons entry entries =>
        obtain ⟨σ', τ', s⟩ := entry
        have hcompat := (List.isChain_cons_cons.mp haxis).1
        change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix
          ((List.ofFn (permutationComposition m n k σ' τ').symm, s) :: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k entries)
          _ picked finish at ht
        cases ht with
        | @cons _ _ _ _ picked _ hs hsb hafter =>
          constructor
          · intro hrows a ha b hb
            have hτ : τ = τ' := by
              rcases hcompat with hσ | hτ
              · exact (hrows (congrArg (fun ρ : Equiv.Perm (Fin (m + 1)) =>
                  List.ofFn ρ.symm) hσ)).elim
              · exact hτ
            subst τ'
            have hlocal := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.horizontal_outer_selections_isChain k σ σ' τ removed _ r s
              (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k entries)
              (by simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable, List.map_cons, List.append_nil] using hfull) hc
            have hpos := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerSelection_bounds k σ' τ _ s hs hsb).1
            have hne := List.length_pos_iff.mp hpos
            change b ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available _
              (List.ofFn (permutationComposition m n k σ' τ).symm)).take s) ++
                (picked.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k)).flatten).head? at hb
            rw [List.head?_append_of_ne_nil _ hne] at hb
            exact (List.isChain_append.mp hlocal).2.2 a ha b hb
          · exact htail

/-- 概要：格子方向だけに動く非退化成功表から非退化な圧縮外側表を復元する（BF §1.5.8）。
方針：元の選択語の外側復元を実際の証跡に固定し、境界条件による圧縮定理を適用する。
規約：復元語自体を出力とし、元の外側行数との一致は別途照合する。
使われ方：一般の TR 部分合成保存の逆構成で元の外側語を供給する。 -/
lemma compressed_outer_table_nondegenerate {m n : ℕ} (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ))
    (removed out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k entries) removed = some out) (hc : out.IsChain (· ≠ ·))
    (haxis : entries.IsChain (fun p q => p.1 = q.1 ∨ p.2.1 = q.2.1)) :
    ∃ picked finish, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k entries) removed picked finish ∧
      out = picked.flatten ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable k entries picked)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed) =
        some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out) ∧ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out).IsChain (· ≠ ·) := by
  obtain ⟨picked, finish, tail, hp, ht, ho⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionPrefix_of_reduceRows
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k entries) [] removed out (by simpa only [List.append_nil] using h)
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_nil, Option.some.injEq] at ht
  subst tail
  have ho' : out = picked.flatten := by simpa only [List.append_nil] using ho
  have hc' : picked.flatten.IsChain (· ≠ ·) := ho' ▸ hc
  have htrace := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable_trace k entries removed finish picked hp
  have hsep := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable_separated k entries removed finish picked hp hc' haxis
  obtain ⟨out', hs, hcollapse, hchain⟩ := htrace.compress_isChain
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable_rows_nodup k entries picked) hsep
  have hx : out' = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out := by
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse out' := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_eq_self out' hchain).symm
      _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (picked.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k)).flatten := hcollapse
      _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k picked.flatten := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.collapse_outer_picked k picked
      _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k out := by rw [ho']
  refine ⟨picked, finish, hp, ho', ?_, ?_⟩
  · simpa only [hx] using hs
  · simpa only [hx] using hchain

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
