module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveOccurrencePosition

/-!
模型。文献の定義との比較は後で
# 同じ語長で読む指定出現の列挙の一致

Berger–Fresse §1.2.4・§2.2.6、M14 L12a。
元の語長移送と同じ出現番号を保ち、元の出現位置と厳密に照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C425：同じ語長の移送は、同じ番号の元の出現位置を保つ（BF §1.2.4）。 -/
lemma word_eq_mp_occurrenceAt {r l l' : ℕ} (h : l = l') (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r l)
    (a : Fin r)
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount
      (Eq.mp (congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r L) h) v).val a))
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v.val a)) (hij : i.val = j.val) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt (Eq.mp (congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r L) h) v).val a i).val =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v.val a j).val := by
  subst l'
  have he : i = j := Fin.ext hij
  subst i
  rfl

/-- C426：元の指定出現をpositiveWordで列挙しても、同じ位置（BF §1.2.4）。 -/
lemma positiveOccurrencePosition_eq {m d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (k : Fin (m + 1)) (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k))
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val k)) (hij : i.val = j.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition u k i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val k j := by
  apply Fin.ext
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.word_eq_mp_occurrenceAt (by omega : (m + 1) + d = m + d + 1) u k j i hij.symm).symm

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
