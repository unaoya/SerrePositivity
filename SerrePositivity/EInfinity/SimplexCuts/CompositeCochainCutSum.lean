module

public import SerrePositivity.EInfinity.SimplexCuts.IteratedNestedCutSum
public import SerrePositivity.EInfinity.Surjection.Composition

/-!
# 元の係数合成の余作用を全合成切断項で読む

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の既存構成の法則、報告 §311。
同じcompositionOnWords・cochainAction・全分割・全Cutを保って評価する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 語長を移した元の合成基底語は、同じ合成切断語そのもの（BF §1.2.4）。 -/
lemma positiveWord_compositeBasisWord {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    positiveWord (r := m + n) (d := d + e)
      (Surjection.compositeBasisWord (m := m) (n := n + 1) (d := d) (e := e)
        u v k r (by omega)) =
      positiveCompositeCutWord u v k r := rfl

/-- 元の合成項を、元の総次数の同じ斉次テンソルで読む（BF §2.2.6）。 -/
lemma positiveCompositeCutTerm_eq_vectorTensorAt (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (x : S _⦋q⦌) :
    positiveCompositeCutTerm A S u v k c x =
      Surjection.compositionSign u v k c.1 •
        (cutSign c.2 (positiveCompositeCutWord u v k c.1).val •
          vectorTensorAt (chains A S) (m + (n + 1))
            (fun a => ⟨outputDegree c.2 (positiveCompositeCutWord u v k c.1) a,
              gen A S (outputDegree c.2 (positiveCompositeCutWord u v k c.1) a)
                (S.map (face c.2 (positiveCompositeCutWord u v k c.1) a).op x)⟩)
            (-((d + e + q : ℕ) : ℤ))
            (by rw [vectorDegree, degreeSum_eq_sum, outputDegree_sum]
                have hn : m + n + (d + e) + q + 1 - (m + (n + 1)) = d + e + q := by omega
                rw [hn])) := by
  let f (a : Fin (m + (n + 1))) : Σ d : ℕ, (chains A S).X (-(d : ℤ)) :=
    ⟨outputDegree c.2 (positiveCompositeCutWord u v k c.1) a,
      gen A S (outputDegree c.2 (positiveCompositeCutWord u v k c.1) a)
        (S.map (face c.2 (positiveCompositeCutWord u v k c.1) a).op x)⟩
  have ht : -(vectorDegree (chains A S) (m + (n + 1)) f : ℤ) = -((d + e + q : ℕ) : ℤ) := by
    change -(degreeSum (m + (n + 1))
      (outputDegree c.2 (positiveCompositeCutWord u v k c.1)) : ℤ) = _
    rw [degreeSum_eq_sum, outputDegree_sum]
    have hn : m + n + (d + e) + q + 1 - (m + (n + 1)) = d + e + q := by omega
    rw [hn]
  unfold positiveCompositeCutTerm cutTerm
  rw [map_zsmul]
  congr 1
  congr 1
  apply eq_of_heq
  apply HEq.trans (module_eqToHom_apply_heq _ _ _ _)
  apply HEq.trans (cutTensorAt_heq_vectorTensor A S c.2 (positiveCompositeCutWord u v k c.1) x)
  exact (vectorTensorAt_heq (chains A S) (m + (n + 1)) f _ ht).symm

/-- 実際の係数合成を作用させた値は、元の全合成切断項の和（BF §1.2.4・§2.2.6）。 -/
lemma cochainAction_composition_cut_sum (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (x : S _⦋q⦌) :
    (cochainAction A S (m + (n + 1))).f (-((d + e + q : ℕ) : ℤ))
      (ιTensorObj (Surjection.complex A (m + (n + 1))) (chains A S)
        (-((d + e : ℕ) : ℤ)) (-(q : ℤ)) (-((d + e + q : ℕ) : ℤ)) (by omega)
        ((Surjection.complexXIso A (m + (n + 1)) (d + e)).inv
          (Surjection.compositionOnWords A u v k) ⊗ₜ[A] gen A S q x)) =
      ∑ c : PositiveCompositeCutIndex u v k q, positiveCompositeCutTerm A S u v k c x := by
  unfold Surjection.compositionOnWords
  simp only [map_sum, map_zsmul, TensorProduct.sum_tmul, ← TensorProduct.smul_tmul']
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  rw [Surjection.compositeGenerator_eq_basis A u v k r (by omega)]
  erw [cochainAction_basis_cut_sum A S (r := m + n) (d := d + e)
      (Surjection.compositeBasisWord (m := m) (n := n + 1) (d := d) (e := e)
        u v k r (by omega)) x _ (by omega)]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [positiveCompositeCutTerm_eq_vectorTensorAt A S u v k ⟨r, s⟩ x]
  simp only [positiveWord_compositeBasisWord]
  rfl

end SerrePositivity.EInfinity.SimplexCuts
