module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryWordLengths
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryCutIndexTransport

/-!
模型。文献の定義との比較は後で
# 元の空語合成の全分割とCutの添字

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §373。
元の語を同じ長さへ移し、全OverlapPartitionの因子を保持する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元の外側語を同じCutの区間数で読む等式移送（BF §2.2.6）。 -/
def nullaryNativeOuterWord {m d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 2) d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word (m + 2) ((m + d) + 2) :=
  Eq.mp (congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word (m + 2) L)
    (by omega : (m + 2) + d = (m + d) + 2)) u

/-- 元の語長の移送は同じ色の出現回数を保つ（BF §1.2.4）。 -/
lemma nullaryNativeOuterWord_count {m d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 2) d)
    (k : Fin (m + 2)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeOuterWord u).val k =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryNativeOuterWord _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount
  exact congrArg (fun l : List (Fin (m + 2)) => l.count k)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.word_eq_mp_ofFn (by omega : (m + 2) + d = (m + d) + 2) u)

/-- 一部分割を同じ部分数の型へ移しても、元の分割は一意（BF §1.2.4）。 -/
lemma overlap_eq_single_of_count_one {n l : ℕ} (hn : n = 1)
    (ρ : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition n l) :
    ρ = Eq.mp (congrArg (fun C => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition C l) hn.symm)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.single l) := by
  subst n
  exact ρ.eq_single

/-- 元の全分割と全小Cut、零項も含む元の全大Cutの直和（BF §2.2.6）。 -/
abbrev NullaryNativeBalanceIndex {m d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 2) d)
    (k : Fin (m + 2)) (q : ℕ) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0 × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + d) q) ⊕
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut ((m + d) + 1) q

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
