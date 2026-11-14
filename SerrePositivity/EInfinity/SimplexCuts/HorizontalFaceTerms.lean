module

public import SerrePositivity.EInfinity.SimplexCuts.HorizontalFaceCoordinates
public import SerrePositivity.EInfinity.SimplexCuts.HorizontalEndpointTerms
public import SerrePositivity.EInfinity.SimplexCuts.DegenerateHorizontalTerms

/-!
# 全水平同値の指定添字で読む元の境界項

Berger–Fresse §2.2.7、M14 L09a。
既存の三分割に沿い、同値が指定する元の文字と小さい切断に値の比較を貼り合わせる。
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

/-- C219：有効な削除は、全水平同値が指定する同じ小さい切断の実項を与える。 -/
lemma outputBoundaryTerm_horizontalBoundaryFaceEquiv_valid {m q r : ℕ} (S : SSet.{0})
    (v : Surjection.Word r (m + 2)) (w : Surjection.Word r (m + 1)) :
    ∀ (c : Fin (m + 2) × Cut m q) (_hw : w.val = Surjection.erase v.val c.1)
      (j : Fin (outputDegree (horizontalBoundaryFaceEquiv m q c).val.1 v
        (label (horizontalBoundaryFaceEquiv m q c).val.1 v.val
          (horizontalBoundaryFaceEquiv m q c).val.2) + 1))
      (_hj : j.val = vertexRank (horizontalBoundaryFaceEquiv m q c).val.1 v.val
        (label (horizontalBoundaryFaceEquiv m q c).val.1 v.val
          (horizontalBoundaryFaceEquiv m q c).val.2) (horizontalBoundaryFaceEquiv m q c).val.2)
      (x : S _⦋q⦌),
    outputBoundaryTerm A S (horizontalBoundaryFaceEquiv m q c).val.1 v
        (label (horizontalBoundaryFaceEquiv m q c).val.1 v.val
          (horizontalBoundaryFaceEquiv m q c).val.2) j x =
      Surjection.deletionCoefficient v.val c.1 •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (horizontalDeletion_degree_eq (q := q) w))).hom (cutTerm A S c.2 w x) := by
  let P (z : MarkedCut (m + 1) q) (a : Fin (m + 2)) (t : Cut m q) : Prop :=
    ∀ (_hw : w.val = Surjection.erase v.val a)
      (j : Fin (outputDegree z.1 v (label z.1 v.val z.2) + 1))
      (_hj : j.val = vertexRank z.1 v.val (label z.1 v.val z.2) z.2) (x : S _⦋q⦌),
      outputBoundaryTerm A S z.1 v (label z.1 v.val z.2) j x =
        Surjection.deletionCoefficient v.val a •
          (eqToHom (congrArg (fun n : ℤ => (power (chains A S) r).X n)
            (horizontalDeletion_degree_eq (q := q) w))).hom (cutTerm A S t w x)
  change ∀ c, P (horizontalBoundaryFaceEquiv m q c).val c.1 c.2
  intro c
  obtain ⟨z, rfl⟩ := (coefficientIndexEndpointEquiv m q).symm.surjective c
  rcases z with t | ⟨t, i⟩ | t
  · rw [coefficientIndexEndpointEquiv_symm_first, horizontalBoundaryFaceEquiv_first]
    dsimp only [P]
    intro hw j hj x
    let e := BarrattEccles.horizontalInsertionEquiv m q 0
    have ht := outputBoundaryTerm_horizontal_first A S (e t).val (e t).property v w hw j hj x
    have hsmall : e.symm ⟨(e t).val, (e t).property⟩ = t := e.symm_apply_apply t
    rw [hsmall] at ht
    exact ht
  · rw [coefficientIndexEndpointEquiv_symm_interior, horizontalBoundaryFaceEquiv_interior]
    dsimp only [P]
    intro hw j hj x
    let b := BarrattEccles.horizontalMarkedEdgeEquiv m q (t, i)
    let a : Fin (m + 1 + q) := Fin.cast (by omega : m + q + 1 = m + 1 + q) b.val.2.castSucc
    let a' : Fin (m + 1 + q) := Fin.cast (by omega : m + q + 1 = m + 1 + q) b.val.2.succ
    let e := BarrattEccles.horizontalInsertionEquiv m q a
    have ha : a ∈ (e t).val.val := (e t).property
    have hb : a' ∈ (e t).val.val := (BarrattEccles.horizontalCornerEquiv m q b).property.2
    have hh : (e t).val.horizontal a.succ = i.castSucc.succ :=
      horizontalInteriorFaceEquiv_horizontal m q t i
    have hw' : w.val = Surjection.erase v.val ((e t).val.horizontal a.succ) := by
      rw [hh]
      exact hw
    have ht := outputBoundaryTerm_horizontalDeletion_valid A S (e t).val v a a'
      (by rfl) ha hb w hw' j hj x
    have hsmall : e.symm ⟨(e t).val, ha⟩ = t := e.symm_apply_apply t
    rw [hh, hsmall] at ht
    exact ht
  · rw [coefficientIndexEndpointEquiv_symm_last, horizontalBoundaryFaceEquiv_last]
    dsimp only [P]
    intro hw j hj x
    let a : Fin (m + 1 + q) := ⟨m + q, by omega⟩
    let e := BarrattEccles.horizontalInsertionEquiv m q a
    have ht := outputBoundaryTerm_horizontal_last A S (e t).val a (e t).property
      (by dsimp [a]; omega) v w hw j hj x
    have hsmall : e.symm ⟨(e t).val, (e t).property⟩ = t := e.symm_apply_apply t
    rw [hsmall] at ht
    exact ht

/-- C220：無効な削除は、全水平同値の同じ指定添字の元の境界項で零となる。 -/
lemma outputBoundaryTerm_horizontalBoundaryFaceEquiv_invalid {m q r : ℕ} (S : SSet.{0})
    (v : Surjection.Word r (m + 2)) (c : Fin (m + 2) × Cut m q)
    (hinvalid : ¬(Function.Surjective (Surjection.erase v.val c.1) ∧
      Surjection.Nondegenerate (Surjection.erase v.val c.1)))
    (j : Fin (outputDegree (horizontalBoundaryFaceEquiv m q c).val.1 v
      (label (horizontalBoundaryFaceEquiv m q c).val.1 v.val
        (horizontalBoundaryFaceEquiv m q c).val.2) + 1)) (x : S _⦋q⦌) :
    outputBoundaryTerm A S (horizontalBoundaryFaceEquiv m q c).val.1 v
      (label (horizontalBoundaryFaceEquiv m q c).val.1 v.val
        (horizontalBoundaryFaceEquiv m q c).val.2) j x = 0 := by
  have hk := ((boundaryVertexKind_eq_horizontal_iff _ _).mp
    (horizontalBoundaryFaceEquiv m q c).property).2
  apply outputBoundaryTerm_horizontal_invalid A S _ v _ hk _ j x
  rw [horizontalBoundaryFaceEquiv_horizontal]
  exact hinvalid

end SerrePositivity.EInfinity.SimplexCuts
