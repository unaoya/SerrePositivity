module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExDegeneracyExpansion
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExDoublePairing

/-!
# pairing の非退化な対応先から元への性質

概要：退化単体の複雑度に合った拡張は退化し、非退化な対応先の元も非退化である。
方針：一つの通常の退化で表示し、その添字と閾値を比較する。
規約：Moss 2020 Lemma 28 の退化性の部分。
使われ方：regular pairing の型 II の条件。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Opposite
open scoped _root_.Simplicial

/--
概要：複雑度の上界を満たす退化単体の、その閾値での拡張は退化する。
方針：通常の退化の添字が閾値より前か後ろかで、対応する交換則を使う。
規約：Moss 2020 Lemma 28。最小閾値という仮定は不要な強い形。
使われ方：非退化な対応先の元の非退化性。
-/
theorem exExpansion_mem_degenerate (X : SSet.{u}) (n : ℕ) (k : Fin (n + 2))
    (s : (SSet.ex.obj X) _⦋n + 1⦌) (hs : s ∈ exComplexity X ⦋n + 1⦌ k)
    (hd : s ∈ (SSet.ex.obj X).degenerate (n + 1)) :
    exExpansion X (n + 1) k s ∈ (SSet.ex.obj X).degenerate (n + 2) := by
  rw [(SSet.ex.obj X).degenerate_eq_iUnion_range_σ] at hd
  obtain ⟨h, t, rfl⟩ := Set.mem_iUnion.mp hd
  have hf : (SSet.ex.obj X).δ h.castSucc ((SSet.ex.obj X).σ h t) = t := by
    exact ConcreteCategory.congr_hom ((SSet.ex.obj X).δ_comp_σ_self (i := h)) t
  by_cases hhk : h.castSucc < k
  · have hk : k ≠ 0 := ne_of_gt ((Fin.zero_le h.castSucc).trans_lt hhk)
    let l := k.pred hk
    have hl : l.succ = k := Fin.succ_pred k hk
    have hh : h ≤ l := by
      change h.val ≤ k.val - 1
      have hv : h.val < k.val := hhk
      omega
    have ht := exComplexity_front_face X n l h.castSucc
      (Fin.castSucc_le_castSucc_iff.mpr hh) ((SSet.ex.obj X).σ h t) (hl.symm ▸ hs)
    rw [hf] at ht
    rw [← hl, exExpansion_front_degeneracy X n h l hh t ht (hl.symm ▸ hs)]
    exact (SSet.ex.obj X).σ_mem_degenerate _ _
  · have hkh : k ≤ h.castSucc := le_of_not_gt hhk
    have hk : k ≠ Fin.last (n + 1) := (hkh.trans_lt h.castSucc_lt_last).ne
    let l := k.castPred hk
    have hl : l.castSucc = k := Fin.castSucc_castPred k hk
    have hh : l ≤ h := Fin.castSucc_le_castSucc_iff.mp (hl.symm ▸ hkh)
    have ht := exComplexity_face X n l h.castSucc ((SSet.ex.obj X).σ h t) (hl.symm ▸ hs)
    rw [hf] at ht
    rw [← hl, exExpansion_rear_degeneracy X n l h hh t ht (hl.symm ▸ hs)]
    exact (SSet.ex.obj X).σ_mem_degenerate _ _

/--
概要：pairing 候補は退化単体を退化単体へ送る。
方針：最小閾値が固定点の上界であることを拡張の退化性に適用する。
規約：Moss 2020 Lemma 28。
使われ方：非退化性を対応先から元へ戻す。
-/
theorem exPairingStep_mem_degenerate (X : SSet.{u}) (n : ℕ)
    (s : (SSet.ex.obj X) _⦋n⦌) (hs : s ∈ (SSet.ex.obj X).degenerate n) :
    exPairingStep X n s ∈ (SSet.ex.obj X).degenerate (n + 1) := by
  cases n with
  | zero => simp at hs
  | succ n => exact exExpansion_mem_degenerate X n _ s (exComplexityLevel_mem X _ s) hs

/--
概要：pairing 候補の対応先が非退化なら元の単体も非退化である。
方針：元が退化すると対応先も退化するという対偶を使う。
規約：Moss 2020 Lemma 28。前段の像に属さないことは ExDoublePairing で証明済み。
使われ方：型 I の元の型 II 条件の非退化性。
-/
theorem exPairingStep_nonDegenerate_source (X : SSet.{u}) (n : ℕ)
    (s : (SSet.ex.obj X) _⦋n⦌)
    (hs : exPairingStep X n s ∈ (SSet.ex.obj X).nonDegenerate (n + 1)) :
    s ∈ (SSet.ex.obj X).nonDegenerate n := by
  rw [(SSet.ex.obj X).mem_nonDegenerate_iff_notMem_degenerate] at hs ⊢
  exact fun hd => hs (exPairingStep_mem_degenerate X n s hd)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
