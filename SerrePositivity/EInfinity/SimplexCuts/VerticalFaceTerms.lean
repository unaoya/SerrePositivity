module

public import SerrePositivity.EInfinity.SimplexCuts.VerticalFaceCoordinates
public import SerrePositivity.EInfinity.SimplexCuts.VerticalInputTerms

/-!
# 全垂直同値の指定入力面で読む元の境界項

Berger–Fresse §2.2.7、M14 L09a。
既存の全垂直同値が選ぶ元の入力面と小さい切断に、実境界項の比較を貼り合わせる。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- C251：全垂直同値の指定面の元の境界項は、同じ入力面の切断項。 -/
lemma outputBoundaryTerm_verticalBoundaryFaceEquiv {m q r : ℕ} (S : SSet.{0})
    (v : Surjection.Word r (m + 1)) (c : Fin (q + 2) × Cut m q)
    (j : Fin (outputDegree (verticalBoundaryFaceEquiv m q c).val.1 v
      (label (verticalBoundaryFaceEquiv m q c).val.1 v.val
        (verticalBoundaryFaceEquiv m q c).val.2) + 1))
    (hj : j.val = vertexRank (verticalBoundaryFaceEquiv m q c).val.1 v.val
      (label (verticalBoundaryFaceEquiv m q c).val.1 v.val
        (verticalBoundaryFaceEquiv m q c).val.2) (verticalBoundaryFaceEquiv m q c).val.2)
    (x : S _⦋q + 1⦌) :
    outputBoundaryTerm A S (verticalBoundaryFaceEquiv m q c).val.1 v
      (label (verticalBoundaryFaceEquiv m q c).val.1 v.val
        (verticalBoundaryFaceEquiv m q c).val.2) j x =
      (-1 : ℤ) ^ (m + 1 - r + c.1.val) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (verticalDeletion_degree_eq (q := q) v))).hom
            (cutTerm A S c.2 v (S.δ c.1 x)) := by
  have ht := outputBoundaryTerm_vertical_of_coordinates A S
    (verticalBoundaryFaceEquiv m q c).val.1 c.2 v
    (verticalBoundaryFaceEquiv m q c).val.2 (verticalBoundaryFaceEquiv m q c).property
    (fun l => (verticalBoundaryFaceEquiv_deleted_coordinates m q c l).1)
    (by intro l; rw [verticalBoundaryFaceEquiv_vertical];
        exact (verticalBoundaryFaceEquiv_deleted_coordinates m q c l).2) j hj x
  simpa only [verticalBoundaryFaceEquiv_vertical] using ht

end SerrePositivity.EInfinity.SimplexCuts
