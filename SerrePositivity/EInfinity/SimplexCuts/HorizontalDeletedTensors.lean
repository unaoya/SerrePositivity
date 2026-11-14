module

public import SerrePositivity.EInfinity.SimplexCuts.DeletedSmallCutTensors
public import SerrePositivity.EInfinity.SimplexCuts.StraightTraceFaces
public import SerrePositivity.EInfinity.SimplexCuts.HorizontalBoundarySigns

/-!
# 内部の水平削除と元の切断テンソル

Berger–Fresse §2.2.6–7、M14 L09a。
指定された水平削除列・次数移送・符号を元の加群で照合する。
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

/-- C190：内部の水平削除の各色の列は、指定された小さい切断の列。 -/
lemma deletedVerticesList_horizontalDeletion {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Fin (m + 2) → Fin r) (a b : Fin (m + 1 + q))
    (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (w : Fin (m + 1) → Fin r) (hw : w = Surjection.erase v (s.horizontal a.succ))
    (c : Fin r) :
    deletedVerticesList s v a.succ c =
      verticesList ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w c := by
  rw [deletedVerticesList_eq_selectColor, horizontal_deletedTrace s v a b hab ha hb,
    verticesList_eq_selectColor, hw]

/-- C191：内部の水平削除の実テンソルを、小さい切断の共通次数の値へ接続。 -/
lemma deletedCutTensor_horizontalDeletion {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (v : Surjection.Word r (m + 2))
    (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val (s.horizontal a.succ))
    (hd : 0 < outputDegree s v (label s v.val a.succ))
    (j : Fin (outputDegree s v (label s v.val a.succ) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val a.succ) a.succ) (x : S _⦋q⦌)
    (h : -((m + q + 1 - r : ℕ) : ℤ) = -((m + 1 + q + 1 - r : ℕ) : ℤ) + 1) :
    deletedCutTensor A S s v (label s v.val a.succ) hd j x =
      (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z) h)).hom
        (cutTensorAt A S ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w x) := by
  exact deletedCutTensor_eq_small_cutTensorAt A S s _ v w a.succ hd
    (deletedVerticesList_horizontalDeletion s v.val a b hab ha hb w.val hw) j hj x h

/-- C192：同じ指定削除の符号付き値は、元の語の係数を掛けた小さい切断項。 -/
lemma signedDeletedCutTensor_horizontalDeletion {m q r : ℕ} (S : SSet.{0})
    (s : Cut (m + 1) q) (v : Surjection.Word r (m + 2))
    (a b : Fin (m + 1 + q)) (hab : b.val = a.val + 1) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (w : Surjection.Word r (m + 1))
    (hw : w.val = Surjection.erase v.val (s.horizontal a.succ))
    (hd : 0 < outputDegree s v (label s v.val a.succ))
    (j : Fin (outputDegree s v (label s v.val a.succ) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val a.succ) a.succ) (x : S _⦋q⦌)
    (h : -((m + q + 1 - r : ℕ) : ℤ) = -((m + 1 + q + 1 - r : ℕ) : ℤ) + 1) :
    outputBoundarySignAt s v a.succ • deletedCutTensor A S s v (label s v.val a.succ) hd j x =
      Surjection.deletionCoefficient v.val (s.horizontal a.succ) •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z) h)).hom
          (cutTerm A S ((BarrattEccles.horizontalInsertionEquiv m q a).symm ⟨s, ha⟩) w x) := by
  rw [deletedCutTensor_horizontalDeletion A S s v a b hab ha hb w hw hd j hj x h,
    outputBoundarySignAt_horizontalDeletion s v a b hab ha hb w hw hd]
  simp only [cutTerm, map_zsmul, mul_smul]

end SerrePositivity.EInfinity.SimplexCuts
