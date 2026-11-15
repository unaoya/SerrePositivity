module

public import SerrePositivity.EInfinity.SimplexCuts.HorizontalDeletedTensors
public import SerrePositivity.EInfinity.SimplexCuts.CornerBoundaryTerms

/-!
# 内部の水平面の元の境界項

Berger–Fresse §2.2.7、M14 L09a。
有効な削除語の全射性から次数の一致を供給し、元の境界項を照合する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- C193：有効な削除語の次数移送は、全射語の既存の長さ評価から従う。 -/
lemma horizontalDeletion_degree_eq {m q r : ℕ} (w : Surjection.Word r (m + 1)) :
    -((m + q + 1 - r : ℕ) : ℤ) = -((m + 1 + q + 1 - r : ℕ) : ℤ) + 1 := by
  have hr := w.arity_le_length
  omega

/-- C194：有効な内部水平面の元の境界項は、指定した小さい切断項に厳密に一致。 -/
lemma outputBoundaryTerm_horizontalDeletion {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (v : Surjection.Word r (m + 2))
    (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val (s.horizontal a.succ))
    (hd : 0 < outputDegree s v (label s v.val a.succ))
    (j : Fin (outputDegree s v (label s v.val a.succ) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val a.succ) a.succ) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val a.succ) j x =
      Surjection.deletionCoefficient v.val (s.horizontal a.succ) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (horizontalDeletion_degree_eq (q := q) w))).hom
          (cutTerm A S ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w x) := by
  unfold outputBoundaryTerm
  rw [dite_eq_left hd, outputBoundarySign_eq_at_of_rank s v a.succ j hj]
  exact signedDeletedCutTensor_horizontalDeletion A S s v a b hab ha hb w hw hd j hj x
    (horizontalDeletion_degree_eq (q := q) w)

end SerrePositivity.EInfinity.SimplexCuts
