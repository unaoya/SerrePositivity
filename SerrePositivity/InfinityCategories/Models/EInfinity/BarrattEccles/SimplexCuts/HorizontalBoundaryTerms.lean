module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalDeletedTensors
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CornerBoundaryTerms

/-!
模型。文献の定義との比較は後で
# 内部の水平面の元の境界項

Berger–Fresse §2.2.7、M14 L09a。
有効な削除語の全射性から次数の一致を供給し、元の境界項を照合する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- C193：有効な削除語の次数移送は、全射語の既存の長さ評価から従う。 -/
lemma horizontalDeletion_degree_eq {m q r : ℕ} (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) :
    -((m + q + 1 - r : ℕ) : ℤ) = -((m + 1 + q + 1 - r : ℕ) : ℤ) + 1 := by
  have hr := w.arity_le_length
  omega

/-- C194：有効な内部水平面の元の境界項は、指定した小さい切断項に厳密に一致。 -/
lemma outputBoundaryTerm_horizontalDeletion {m q r : ℕ} (S : SSet.{0})
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 2))
    (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1))
    (hw : w.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v.val (s.horizontal a.succ))
    (hd : 0 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val a.succ))
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val a.succ) + 1))
    (hj : j.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexRank s v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val a.succ) a.succ) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm A S s v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.label s v.val a.succ) j x =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v.val (s.horizontal a.succ) •
        (eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r).X z)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalDeletion_degree_eq (q := q) w))).hom
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm A S ((_root_.SerrePositivity.EInfinity.BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w x) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm
  rw [dite_eq_left hd, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundarySign_eq_at_of_rank s v a.succ j hj]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.signedDeletedCutTensor_horizontalDeletion A S s v a b hab ha hb w hw hd j hj x
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalDeletion_degree_eq (q := q) w)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
