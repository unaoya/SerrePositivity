module

public import SerrePositivity.EInfinity.SimplexCuts.HorizontalDeletionCoordinates
public import SerrePositivity.EInfinity.SimplexCuts.HorizontalVertexKinds
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleFirstFace

/-!
# 水平な始端と終端の元の境界項

Berger–Fresse §2.2.4・§2.2.7、M14 L09a。
既存の端点の座標公式を同じ削除列・実テンソル・符号の比較へ接続する。
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

/-- C199：水平削除の指定座標から、元の境界項の厳密な比較を得る。 -/
lemma outputBoundaryTerm_horizontal_of_coordinates {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (t : Cut m q)
    (v : Surjection.Word r (m + 2)) (w : Surjection.Word r (m + 1))
    (k : Fin (m + 1 + q + 1)) (a : Fin (m + 2)) (hk : s.horizontal k = a)
    (hsingle : ∀ l, s.horizontal l = a → l = k)
    (hw : w.val = Surjection.erase v.val a)
    (hh : ∀ l : Fin (m + q + 1),
      s.horizontal (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) l)) =
        a.succAbove (t.horizontal l))
    (hv : ∀ l : Fin (m + q + 1),
      s.vertical (k.succAbove (Fin.cast (by omega : m + q + 1 = m + 1 + q) l)) = t.vertical l)
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val k) j x =
      Surjection.deletionCoefficient v.val a •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (horizontalDeletion_degree_eq (q := q) w))).hom (cutTerm A S t w x) := by
  have hl : ∀ c, deletedVerticesList s v.val k c = verticesList t w.val c := by
    intro c
    rw [deletedVerticesList_eq_selectColor,
      deletedTrace_eq_of_horizontal_coordinates s t v.val k a hh hv,
      verticesList_eq_selectColor, hw]
  have hd := outputDegree_pos_of_deleted_vertexLists s t v w k hl
  have hs := outputBoundarySignAt_horizontal_of_coordinates s t v w a k hk hsingle hd
    (hi_eq_of_horizontal_deleted_coordinates s t k a hk hh hv) hw (by
      intro l
      rw [hw]
      change v.val (s.horizontal (k.succAbove l)) =
        v.val (a.succAbove (t.horizontal (Fin.cast (by omega) l)))
      have hc : Fin.cast (by omega : m + q + 1 = m + 1 + q)
          (Fin.cast (by omega : m + 1 + q = m + q + 1) l) = l := Fin.ext rfl
      exact congrArg v.val (by simpa only [hc] using hh (Fin.cast (by omega) l)))
  unfold outputBoundaryTerm
  rw [dite_eq_left hd, outputBoundarySign_eq_at_of_rank s v k j hj, hs,
    deletedCutTensor_eq_small_cutTensorAt A S s t v w k hd hl j hj x
      (horizontalDeletion_degree_eq (q := q) w)]
  simp only [cutTerm, map_zsmul, mul_smul]

/-- C200：水平始端の元の境界項は、最初の文字を削除した切断項。 -/
lemma outputBoundaryTerm_horizontal_first {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (h₀ : (0 : Fin (m + 1 + q)) ∈ s.val)
    (v : Surjection.Word r (m + 2)) (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val 0)
    (j : Fin (outputDegree s v (label s v.val 0) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val 0) 0) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val 0) j x =
      Surjection.deletionCoefficient v.val 0 •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (horizontalDeletion_degree_eq (q := q) w))).hom
          (cutTerm A S ((BarrattEccles.horizontalInsertionEquiv m q 0).symm ⟨s, h₀⟩) w x) := by
  have hsingle := (horizontal_fiber_singleton_iff s 0).mpr
    ((horizontalVertex_zero_iff s (by omega)).mpr h₀)
  refine outputBoundaryTerm_horizontal_of_coordinates A S s _ v w 0 0
    s.horizontal_endpoints.1
    (by simpa only [s.horizontal_endpoints.1] using hsingle) hw ?_ ?_ j hj x
  · intro l
    have hc : Fin.cast (by omega : m + 1 + q = m + q + 1)
        (Fin.cast (by omega : m + q + 1 = m + 1 + q) l) = l := Fin.ext rfl
    simpa only [Fin.succAbove_zero, hc] using BarrattEccles.horizontalDeletion_first_horizontal
      s h₀ (Fin.cast (by omega) l)
  · intro l
    have hc : Fin.cast (by omega : m + 1 + q = m + q + 1)
        (Fin.cast (by omega : m + q + 1 = m + 1 + q) l) = l := Fin.ext rfl
    simpa only [Fin.succAbove_zero, hc] using BarrattEccles.horizontalDeletion_first_vertical
      s h₀ (Fin.cast (by omega) l)

/-- C201：水平終端の元の境界項は、最後の文字を削除した切断項。 -/
lemma outputBoundaryTerm_horizontal_last {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (a : Fin (m + 1 + q)) (ha : a ∈ s.val)
    (hlast : a.val + 1 = m + 1 + q)
    (v : Surjection.Word r (m + 2)) (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val (Fin.last (m + 1)))
    (j : Fin (outputDegree s v (label s v.val (Fin.last (m + 1 + q))) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val (Fin.last (m + 1 + q)))
      (Fin.last (m + 1 + q))) (x : S _⦋q⦌) :
    outputBoundaryTerm A S s v (label s v.val (Fin.last (m + 1 + q))) j x =
      Surjection.deletionCoefficient v.val (Fin.last (m + 1)) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z)
          (horizontalDeletion_degree_eq (q := q) w))).hom
          (cutTerm A S ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w x) := by
  have hk : a.succ = Fin.last (m + 1 + q) := Fin.ext hlast
  have he : (⟨m + 1 + q - 1, by omega⟩ : Fin (m + 1 + q)) = a := by
    apply Fin.ext
    change m + 1 + q - 1 = a.val
    omega
  have hH : HorizontalVertex s (Fin.last (m + 1 + q)) :=
    (horizontalVertex_last_iff s (by omega)).mpr (by simpa only [he] using ha)
  have hsingle := (horizontal_fiber_singleton_iff s (Fin.last (m + 1 + q))).mpr hH
  refine outputBoundaryTerm_horizontal_of_coordinates A S s _ v w _ _
    s.horizontal_endpoints.2
    (by simpa only [s.horizontal_endpoints.2] using hsingle) hw ?_ ?_ j hj x
  · intro l
    have hc : Fin.cast (by omega : m + 1 + q = m + q + 1)
        (Fin.cast (by omega : m + q + 1 = m + 1 + q) l) = l := Fin.ext rfl
    simpa only [hk, hc] using BarrattEccles.horizontalDeletion_last s a ha hlast
      (Fin.cast (by omega) l)
  · intro l
    have hc : Fin.cast (by omega : m + 1 + q = m + q + 1)
        (Fin.cast (by omega : m + q + 1 = m + 1 + q) l) = l := Fin.ext rfl
    simpa only [hk, hc] using BarrattEccles.horizontalDeletion_vertical s a ha
      (Fin.cast (by omega) l)

end SerrePositivity.EInfinity.SimplexCuts
