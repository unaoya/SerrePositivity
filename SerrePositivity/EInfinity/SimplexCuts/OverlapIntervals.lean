module

public import SerrePositivity.EInfinity.Surjection.OverlapPartition
public import Mathlib.Algebra.BigOperators.Fin

/-!
# 同じ共有端点を持つ部分区間の長さの総和

Berger–Fresse §1.2.4、M14 L12a の分割の復元。
元の始点・終点の有限和を望遠和にして、既存OverlapPartitionの総長条件へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C374：同じ共有端点の部分長の総和は、元の語長と部分数で決まる（BF §1.2.4）。 -/
lemma intervalLengths_sum (t L : ℕ) (a b : Fin (t + 1) → ℕ)
    (hab : ∀ j, a j ≤ b j) (hfirst : a 0 = 0) (hlast : b (Fin.last t) + 1 = L)
    (hnext : ∀ i : Fin t, b i.castSucc = a i.succ) :
    (∑ j : Fin (t + 1), (b j - a j + 1)) + 1 = L + (t + 1) := by
  have hs : (∑ j : Fin (t + 1), (b j - a j)) + (∑ j : Fin (t + 1), a j) =
      ∑ j : Fin (t + 1), b j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => Nat.sub_add_cancel (hab j))
  have hA : (∑ j : Fin (t + 1), a j) = ∑ j : Fin t, a j.succ := by
    rw [Fin.sum_univ_succ, hfirst, zero_add]
  have hB : (∑ j : Fin (t + 1), b j) = (∑ j : Fin t, a j.succ) + b (Fin.last t) := by
    rw [Fin.sum_univ_castSucc]
    exact congrArg (fun z => z + b (Fin.last t))
      (Finset.sum_congr rfl (fun j _ => hnext j))
  have hlen : (∑ j : Fin (t + 1), (b j - a j + 1)) =
      (∑ j : Fin (t + 1), (b j - a j)) + (t + 1) := by
    simp [Finset.sum_add_distrib]
  rw [hA, hB] at hs
  omega

/-- 元の部分長から、同じ既存の重なる分割を作る（BF §1.2.4）。 -/
def overlapOfIntervals {t L : ℕ} (ht : 0 < t) (a b : Fin t → ℕ)
    (hab : ∀ j, a j ≤ b j) (hb : ∀ j, b j < L)
    (hfirst : ∀ j, j.val = 0 → a j = 0)
    (hlast : ∀ j, j.val + 1 = t → b j + 1 = L)
    (hnext : ∀ i j, i.val + 1 = j.val → b i = a j) : Surjection.OverlapPartition t L := by
  refine ⟨fun j => ⟨b j - a j + 1, by have h := hb j; omega⟩, ?_, ?_⟩
  · intro j
    exact Or.inl (Nat.succ_pos _)
  · change (∑ j : Fin t, (b j - a j + 1)) + 1 = L + t
    cases t with
    | zero => omega
    | succ t =>
      exact intervalLengths_sum t L a b hab (hfirst 0 rfl) (hlast (Fin.last t) rfl)
        (fun i => hnext i.castSucc i.succ rfl)

end SerrePositivity.EInfinity.SimplexCuts
