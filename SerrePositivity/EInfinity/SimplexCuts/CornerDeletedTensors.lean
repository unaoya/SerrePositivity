module

public import SerrePositivity.EInfinity.SimplexCuts.DeletedFaceTensors

/-!
# 混合角の実際の削除テンソルの一致

Berger–Fresse §2.2.7、M14 L09a。
指定面の厳密な一致から同じ正規化生成元を読み、全体の次数移送まで合わせる。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- C162：更新次数と指定面の一致から、元の実際の削除テンソルが一致する。 -/
lemma deletedCutTensor_eq_of_faces {m q r : ℕ} (S : SSet.{0}) (s t : Cut m q)
    (v : Surjection.Word r (m + 1)) (a b : Fin r)
    (ha : 0 < outputDegree s v a) (hb : 0 < outputDegree t v b)
    (ja : Fin (outputDegree s v a + 1)) (jb : Fin (outputDegree t v b + 1))
    (he : Function.update (outputDegree s v) a (outputDegree s v a - 1) =
      Function.update (outputDegree t v) b (outputDegree t v b - 1))
    (hf : ∀ c, deletedCutFace s v a ha ja c =
      eqToHom (congrArg SimplexCategory.mk (congrFun he c)) ≫ deletedCutFace t v b hb jb c)
    (x : S _⦋q⦌) : deletedCutTensor A S s v a ha ja x =
      deletedCutTensor A S t v b hb jb x := by
  have hda := degreeSum_delete (outputDegree s v) a ha
  have hdb := degreeSum_delete (outputDegree t v) b hb
  have hsa := (degreeSum_eq_sum r (outputDegree s v)).trans (outputDegree_sum s v)
  have hsb := (degreeSum_eq_sum r (outputDegree t v)).trans (outputDegree_sum t v)
  have hta : -(degreeSum r (Function.update (outputDegree s v) a
      (outputDegree s v a - 1)) : ℤ) = -((m + q + 1 - r : ℕ) : ℤ) + 1 := by omega
  have htb : -(degreeSum r (Function.update (outputDegree t v) b
      (outputDegree t v b - 1)) : ℤ) = -((m + q + 1 - r : ℕ) : ℤ) + 1 := by omega
  rw [deletedCutTensor_eq_faces A S s v a ha ja x hta,
    deletedCutTensor_eq_faces A S t v b hb jb x htb]
  refine tensorValue_cast_target_congr A _ _ _ _ he _ _ ?_ _ hta htb
  intro c
  rw [hf c]
  exact gen_cast_source A S (congrFun he c) (deletedCutFace t v b hb jb c) x

/-- C163：混合角の両側の元の実際の削除テンソルは厳密に一致。 -/
lemma deletedCutTensor_swapSteps {m q r : ℕ} (S : SSet.{0}) (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a b : Fin (m + q)) (hab : b.val = a.val + 1)
    (ho : 0 < outputDegree s v (label s v.val b.castSucc))
    (hn : 0 < outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc))
    (jo : Fin (outputDegree s v (label s v.val b.castSucc) + 1))
    (jno : jo.val = vertexRank s v.val (label s v.val b.castSucc) b.castSucc)
    (jn : Fin (outputDegree (s.swapSteps a b) v (label (s.swapSteps a b) v.val b.castSucc) + 1))
    (jnn : jn.val = vertexRank (s.swapSteps a b) v.val
      (label (s.swapSteps a b) v.val b.castSucc) b.castSucc) (x : S _⦋q⦌) :
    deletedCutTensor A S (s.swapSteps a b) v
        (label (s.swapSteps a b) v.val b.castSucc) hn jn x =
      deletedCutTensor A S s v (label s v.val b.castSucc) ho jo x := by
  apply deletedCutTensor_eq_of_faces A S _ _ v _ _ hn ho jn jo
    (deletedOutputDegree_swapSteps s v a b hab ho hn)
  exact deletedCutFace_swapSteps s v a b hab ho hn jo jno jn jnn

end SerrePositivity.EInfinity.SimplexCuts
