module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CoefficientLengthTransports

/-!
模型。文献の定義との比較は後で
# 同じpositiveWordと元の係数語の照合

Berger–Fresse §1.2.3・§2.2.7、M14 L09の証明分割。
既存の語長の等式移送を、positiveWordの値・文字削除・削除係数へ適用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C291：同じpositiveWordの値は、元の語の等式移送。 -/
lemma positiveWord_cast_val {r d : ℕ} (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w).val = fun i : Fin (r + d + 1) =>
      w.val (Fin.cast (by omega : r + d + 1 = (r + 1) + d) i) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.word_cast_val (by omega : (r + 1) + d = r + d + 1) w

/-- C292：同じ指定位置の文字削除は、positiveWordの語長の移送と可換。 -/
lemma erase_positiveWord {r d : ℕ} (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) (d + 1))
    (a : Fin ((r + 1) + (d + 1))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w).val
        (Fin.cast (by omega : (r + 1) + (d + 1) = r + d + 2) a) =
      fun i : Fin (r + d + 1) => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase w.val a
        (Fin.cast (by omega : r + d + 1 = (r + 1) + d) i) := by
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.erase_cast_length (by omega : (r + 1) + d = r + d + 1) w.val a
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord_cast_val]
  convert ht using 1

/-- C293：同じ指定位置の削除係数は、positiveWordの語長の移送で変わらない。 -/
lemma deletionCoefficient_positiveWord {r d : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) (d + 1)) (a : Fin ((r + 1) + (d + 1))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w).val
        (Fin.cast (by omega : (r + 1) + (d + 1) = r + d + 2) a) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient w.val a := by
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.deletionCoefficient_cast_length
    (by omega : (r + 1) + (d + 1) = r + d + 2) w.val a
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord_cast_val]
  convert ht using 1

/-- C296：同じ切断用の語を元の語長へ戻してからpositiveWordへ移すと、その語自身。 -/
lemma positiveWord_of_cast {r d : ℕ} (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word (r + 1) (r + d + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord (Eq.mp (congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word (r + 1))
      (by omega : r + d + 1 = (r + 1) + d)) w) = w := by
  have hl : r + d + 1 = (r + 1) + d := by omega
  apply Subtype.ext
  funext i
  calc
    _ = w.val (Fin.cast hl.symm (Fin.cast hl i)) := by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord_cast_val, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.word_cast_val hl]
    _ = w.val i := congrArg w.val (Fin.ext rfl)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
