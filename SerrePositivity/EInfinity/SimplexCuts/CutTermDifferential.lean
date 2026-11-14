module

public import SerrePositivity.EInfinity.SimplexCuts.PositiveOutputFactor

/-!
# 同じ切断項の微分と指定出力境界の全和

Berger–Fresse §2.2.7、M14 L09の証明分割。
既存の純粋テンソルの微分則を、零次数の因子も含む同じ実出力境界項へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- C281：出力次数零の因子の同じテンソル微分の成分は零。 -/
lemma tensorValueDifferentialFactor_cut_zero (S : SSet.{0}) {m q r : ℕ}
    (s : Cut m q) (v : Surjection.Word r (m + 1)) (a : Fin r)
    (ha : outputDegree s v a = 0) (x : S _⦋q⦌) :
    tensorValueDifferentialFactor (chains A S) r (outputDegree s v)
      (fun b => gen A S (outputDegree s v b) (S.map (face s v b).op x)) a = 0 := by
  have hg (p : ℕ) (hp : p = 0) (y : S _⦋p⦌) :
      (chains A S).d (-(p : ℤ)) (-(p : ℤ) + 1) (gen A S p y) = 0 := by
    subst p
    exact gen_d_zero A S y
  exact tensorValueDifferentialFactor_eq_zero_of_closed (chains A S) r (outputDegree s v)
    (fun b => gen A S (outputDegree s v b) (S.map (face s v b).op x)) a
    (hg _ ha (S.map (face s v a).op x))

/-- C257：同じ切断項の微分は、全指定出力面の同じ実境界値の和。 -/
lemma cutTerm_d_eq_sum_outputBoundaryTerm (S : SSet.{0})
    {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1)) (x : S _⦋q⦌) :
    (power (chains A S) r).d (-((m + q + 1 - r : ℕ) : ℤ))
        (-((m + q + 1 - r : ℕ) : ℤ) + 1) (cutTerm A S s v x) =
      ∑ a : Fin r, ∑ j : Fin (outputDegree s v a + 1),
        outputBoundaryTerm A S s v a j x := by
  let K := chains A S
  let d := outputDegree s v
  have h0 : -(degreeSum r d : ℤ) = -((m + q + 1 - r : ℕ) : ℤ) := by
    dsimp only [d]
    rw [degreeSum_eq_sum, outputDegree_sum]
  have h1 : -(degreeSum r d : ℤ) + 1 = -((m + q + 1 - r : ℕ) : ℤ) + 1 := by rw [h0]
  have hc : (power K r).d (-((m + q + 1 - r : ℕ) : ℤ))
      (-((m + q + 1 - r : ℕ) : ℤ) + 1) (cutTerm A S s v x) =
      cutSign s v.val •
        (eqToHom (congrArg (fun z : ℤ => (power K r).X z) h1)).hom
          ((power K r).d (-(degreeSum r d : ℤ)) (-(degreeSum r d : ℤ) + 1)
            (cutTensor A S s v x)) := by
    have ht := complex_d_cast_source_target A (power K r)
      (i := -(degreeSum r d : ℤ)) (i' := -((m + q + 1 - r : ℕ) : ℤ))
      (j := -(degreeSum r d : ℤ) + 1) (j' := -((m + q + 1 - r : ℕ) : ℤ) + 1)
      h0 h1 (cutTensor A S s v x)
    dsimp only [cutTerm, cutTensorAt]
    rw [map_zsmul]
    convert congrArg (fun y => cutSign s v.val • y) ht using 1
  rw [hc]
  dsimp only [cutTensor]
  rw [tensorValue_d_sum]
  simp only [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : 0 < outputDegree s v a
  · rw [cast_tensorValueDifferentialFactor_eq_sum_deletedCutTensor A S s v a ha x h1]
    simp only [Finset.smul_sum, outputBoundaryTerm, dite_eq_left ha, outputBoundarySign, mul_smul]
  · have hz : outputDegree s v a = 0 := by omega
    rw [tensorValueDifferentialFactor_cut_zero A S s v a hz x, map_zero, smul_zero]
    simp only [outputBoundaryTerm, dite_eq_right ha, Finset.sum_const_zero]

end SerrePositivity.EInfinity.SimplexCuts
