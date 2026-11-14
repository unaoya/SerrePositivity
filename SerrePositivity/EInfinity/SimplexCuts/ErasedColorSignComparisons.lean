module

public import SerrePositivity.EInfinity.SimplexCuts.ErasedBoundarySigns

/-!
# 同じ削除色列の逆転符号の比較

Berger–Fresse §2.2.4・§2.2.7、M14 L09a。
有限順序の長さだけを移した同じ色列のcaesura逆転数は変わらない。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts
open SerrePositivity.EInfinity.IntervalCuts (positionInversionCount)

/-- 同じ色列を長さの等式で移しても、そのcaesuraの逆転数は変わらない。 -/
lemma caesuraInversionCount_congr_length {N M r : ℕ} (h : N = M)
    (v : Fin N → Fin r) (w : Fin M → Fin r)
    (he : ∀ i, v i = w (Fin.cast h i)) :
    positionInversionCount v (caesuraPositions v) =
      positionInversionCount w (caesuraPositions w) := by
  subst M
  have hv : v = w := funext fun i => by simpa only [Fin.cast_refl, id_eq] using he i
  rw [hv]

/-- C180：削除した色列が小さい切断の展開色列なら、逆転符号はその切断のもの。 -/
lemma erasedColorSign_eq_permutationSign {m q n q' r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (k : Fin (m + q + 1)) (t : Cut n q')
    (w : Fin (n + 1) → Fin r) (h : m + q = n + q' + 1)
    (he : ∀ i, Surjection.erase (label s v) k i = label t w (Fin.cast h i)) :
    erasedColorSign (label s v) k = (-1 : ℤ) ^ permutationExponent t w := by
  unfold erasedColorSign
  rw [permutationExponent_eq_active_inversions]
  apply congrArg (fun j : ℕ => (-1 : ℤ) ^ j)
  exact caesuraInversionCount_congr_length h _ _ he

end SerrePositivity.EInfinity.SimplexCuts
