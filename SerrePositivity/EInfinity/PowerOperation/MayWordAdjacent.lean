module

public import SerrePositivity.EInfinity.PowerOperation.CyclicTensorMixedWords
public import SerrePositivity.GroupTheory.Coxeter.TypeA

/-!
# May の混合入力の語の隣接交換

May, Proposition 2.3(ii) の巡回軌道表示の補助。
既存の二色語の再帰と、既存の対称群作用の同じ隣接交換を照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.PowerOperation
open SerrePositivity.Coxeter

/-- 既存の二色語の先頭に、指定した色を付ける。 -/
def mayWordCons (n : ℕ) (c : Bool) (w : BinaryTensorWord n) : BinaryTensorWord (n + 1) :=
  if c then .inr w else .inl w

lemma mayWordCons_surjective (n : ℕ) (w : BinaryTensorWord (n + 1)) :
    ∃ (c : Bool) (v : BinaryTensorWord n), mayWordCons n c v = w := by
  cases w with
  | inl v => exact ⟨false, v, rfl⟩
  | inr v => exact ⟨true, v, rfl⟩

lemma mayWordCons_colors (n : ℕ) (c : Bool) (w : BinaryTensorWord n) :
    binaryTensorWordColors (n + 1) (mayWordCons n c w) =
      Fin.cons c (binaryTensorWordColors n w) := by
  cases c <;> rfl

/-- 先頭の隣接交換は、同じ再帰的な語の先頭二色を交換する。 -/
lemma mayWordCons_swapFirst (n : ℕ) (c d : Bool) (w : BinaryTensorWord n) :
    adjacentTransposition (0 : Fin (n + 1)) • mayWordCons (n + 1) c (mayWordCons n d w) =
      mayWordCons (n + 1) d (mayWordCons n c w) := by
  apply (binaryTensorWordColorsEquiv (n + 2)).injective
  funext i
  change binaryTensorWordColors (n + 2) _ i = binaryTensorWordColors (n + 2) _ i
  rw [binaryTensorWordColors_smul]
  simp only [mayWordCons_colors]
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i
  · simp [adjacentTransposition]
  · simp [adjacentTransposition]
  · have h1 : l.succ.succ ≠ (0 : Fin (n + 1)).succ := by
      intro he
      exact Fin.succ_ne_zero l ((Fin.succ_inj).mp he)
    have h1' : l.succ.succ ≠ (1 : Fin (n + 2)) := by
      simpa only [Fin.succ_zero_eq_one'] using h1
    simp [adjacentTransposition, Equiv.swap_apply_def, h1']

/-- 尾の隣接交換は先頭の色を保つ。 -/
lemma mayWordCons_swapTail (n : ℕ) (i : Fin n) (c : Bool) (w : BinaryTensorWord (n + 1)) :
    adjacentTransposition i.succ • mayWordCons (n + 1) c w =
      mayWordCons (n + 1) c (adjacentTransposition i • w) := by
  apply (binaryTensorWordColorsEquiv (n + 2)).injective
  funext j
  change binaryTensorWordColors (n + 2) _ j = binaryTensorWordColors (n + 2) _ j
  rw [binaryTensorWordColors_smul]
  simp only [mayWordCons_colors]
  refine Fin.cases ?_ (fun l => ?_) j
  · have h0 : (0 : Fin (n + 2)) ≠ i.castSucc.succ := (Fin.succ_ne_zero _).symm
    have h1 : (0 : Fin (n + 2)) ≠ i.succ.succ := (Fin.succ_ne_zero _).symm
    simp [adjacentTransposition, Equiv.swap_apply_def, h0, h1]
  · by_cases h0 : l = i.castSucc
    · simp [adjacentTransposition, binaryTensorWordColors_smul, h0]
    · by_cases h1 : l = i.succ <;>
        simp [adjacentTransposition, Equiv.swap_apply_def, binaryTensorWordColors_smul, h0, h1]

end SerrePositivity.EInfinity.PowerOperation
