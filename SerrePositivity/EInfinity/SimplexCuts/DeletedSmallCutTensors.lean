module

public import SerrePositivity.EInfinity.SimplexCuts.HorizontalDeletedFaces
public import SerrePositivity.EInfinity.SimplexCuts.DeletedFaceTensors
public import SerrePositivity.EInfinity.SimplexCuts.SignedTerms

/-!
# 小さい切断の実テンソルと削除した出力の一致

Berger–Fresse §2.2.6–7、M14 L09a。
同じ削除列の次数と指定面を、元の純粋テンソルと共通次数への移送へ接続する。
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

/-- C187：同じ削除列の小さい切断の全出力次数は、一だけ小さい。 -/
lemma degreeSum_deleted_small_cut {m n q r : ℕ} (s : Cut m q) (t : Cut n q)
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (hl : ∀ c, deletedVerticesList s v.val k c = verticesList t w.val c) :
    degreeSum r (outputDegree t w) + 1 = m + q + 1 - r := by
  have h := degreeSum_delete (outputDegree s v) (label s v.val k) hd
  rw [deletedOutputDegree_eq_of_vertexLists s t v w k hd hl] at h
  exact h.trans ((degreeSum_eq_sum r (outputDegree s v)).trans (outputDegree_sum s v))

/-- C188：同じ削除列の指定面を、元の小さい切断の実テンソルへ接続する。 -/
lemma deletedCutTensor_eq_small_cutTensor {m n q r : ℕ} (S : SSet.{0})
    (s : Cut m q) (t : Cut n q)
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (hl : ∀ c, deletedVerticesList s v.val k c = verticesList t w.val c)
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (x : S _⦋q⦌)
    (h : -(degreeSum r (outputDegree t w) : ℤ) = -((m + q + 1 - r : ℕ) : ℤ) + 1) :
    deletedCutTensor A S s v (label s v.val k) hd j x =
      (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z) h)).hom
        (cutTensor A S t w x) := by
  have he := deletedOutputDegree_eq_of_vertexLists s t v w k hd hl
  have hs : -(degreeSum r (Function.update (outputDegree s v) (label s v.val k)
      (outputDegree s v (label s v.val k) - 1)) : ℤ) =
      -((m + q + 1 - r : ℕ) : ℤ) + 1 := by rw [he]; exact h
  rw [deletedCutTensor_eq_faces A S s v _ hd j x hs]
  unfold cutTensor
  refine tensorValue_cast_target_congr A _ _ _ _ he _ _ ?_ _ hs h
  intro c
  rw [deletedCutFace_eq_of_vertexLists s t v w k hd hl j hj c]
  exact gen_cast_source A S (congrFun he c) (face t w c) x

/-- C189：同じ比較を、元のcutTermで使う共通次数の実テンソルへ運ぶ。 -/
lemma deletedCutTensor_eq_small_cutTensorAt {m n q r : ℕ} (S : SSet.{0})
    (s : Cut m q) (t : Cut n q)
    (v : Surjection.Word r (m + 1)) (w : Surjection.Word r (n + 1))
    (k : Fin (m + q + 1)) (hd : 0 < outputDegree s v (label s v.val k))
    (hl : ∀ c, deletedVerticesList s v.val k c = verticesList t w.val c)
    (j : Fin (outputDegree s v (label s v.val k) + 1))
    (hj : j.val = vertexRank s v.val (label s v.val k) k) (x : S _⦋q⦌)
    (h : -((n + q + 1 - r : ℕ) : ℤ) = -((m + q + 1 - r : ℕ) : ℤ) + 1) :
    deletedCutTensor A S s v (label s v.val k) hd j x =
      (eqToHom (congrArg (fun z : ℤ => (power (chains A S) r).X z) h)).hom
        (cutTensorAt A S t w x) := by
  have hr : -(degreeSum r (outputDegree t w) : ℤ) =
      -((m + q + 1 - r : ℕ) : ℤ) + 1 := by
    rw [degreeSum_eq_sum, outputDegree_sum]
    exact h
  rw [deletedCutTensor_eq_small_cutTensor A S s t v w k hd hl j hj x hr]
  unfold cutTensorAt
  have step {M N P : ModuleCat A} (hMN : M = N) (hNP : N = P) (y : M) :
      (eqToHom hNP).hom ((eqToHom hMN).hom y) = (eqToHom (hMN.trans hNP)).hom y := by
    subst N
    subst P
    rfl
  rw [step]

end SerrePositivity.EInfinity.SimplexCuts
