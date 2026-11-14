module

public import SerrePositivity.EInfinity.SimplexCuts.HorizontalBoundaryTerms

/-!
# 有効な水平削除語の指定境界項

Berger–Fresse §2.2.7、M14 L09a。
既存の色別リストの長さから正の出力次数を供給し、同じ指定境界項を包装する。
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

/-- C195：有効な小さい切断と同じ削除列なら、削除元の色の出力次数は正。 -/
lemma outputDegree_pos_of_deleted_vertexLists {m n q r : ℕ} (s : Cut m q) (t : Cut n q)
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1))
    (hl : ∀ c, deletedVerticesList s v.val k c = verticesList t w.val c) :
    0 < outputDegree s v (label s v.val k) := by
  have h := congrArg List.length (hl (label s v.val k))
  rw [deletedVerticesList_length, ite_eq_left rfl, verticesList_length] at h
  omega

/-- C196：有効な内部水平削除の実境界項。出力の正次数も既存の列の一致から供給。 -/
lemma outputBoundaryTerm_horizontalDeletion_valid {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (v : Surjection.Word r (m + 2))
    (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val (s.horizontal a.succ))
    (j : Fin (outputDegree s v (label s v.val a.succ) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val a.succ) a.succ) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val a.succ) j x =
      Surjection.deletionCoefficient v.val (s.horizontal a.succ) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (horizontalDeletion_degree_eq (q := q) w))).hom
          (cutTerm A S ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w x) := by
  apply outputBoundaryTerm_horizontalDeletion A S s v a b hab ha hb w hw _ j hj x
  exact outputDegree_pos_of_deleted_vertexLists s _ v w a.succ
    (deletedVerticesList_horizontalDeletion s v.val a b hab ha hb w.val hw)

end SerrePositivity.EInfinity.SimplexCuts
