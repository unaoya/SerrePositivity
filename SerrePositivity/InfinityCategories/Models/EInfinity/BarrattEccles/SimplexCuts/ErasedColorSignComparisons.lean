module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.ErasedBoundarySigns

/-!
模型。文献の定義との比較は後で
# 同じ削除色列の逆転符号の比較

Berger–Fresse §2.2.4・§2.2.7、M14 L09a。
有限順序の長さだけを移した同じ色列のcaesura逆転数は変わらない。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts (positionInversionCount)

/-- 同じ色列を長さの等式で移しても、そのcaesuraの逆転数は変わらない。 -/
lemma caesuraInversionCount_congr_length {N M r : ℕ} (h : N = M)
    (v : Fin N → Fin r) (w : Fin M → Fin r)
    (he : ∀ i, v i = w (Fin.cast h i)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions v) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraPositions w) := by
  subst M
  have hv : v = w := funext fun i => by simpa only [Fin.cast_refl, id_eq] using he i
  rw [hv]

/-- C180：削除した色列が小さい切断の展開色列なら、逆転符号はその切断のもの。 -/
lemma erasedColorSign_eq_permutationSign {m q n q' r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : Fin (m + 1) → Fin r) (k : Fin (m + q + 1)) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut n q')
    (w : Fin (n + 1) → Fin r) (h : m + q = n + q' + 1)
    (he : ∀ i, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v) k i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label t w (Fin.cast h i)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.erasedColorSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v) k = (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.permutationExponent t w := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.erasedColorSign
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.permutationExponent_eq_active_inversions]
  apply congrArg (fun j : ℕ => (-1 : ℤ) ^ j)
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesuraInversionCount_congr_length h _ _ he

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
