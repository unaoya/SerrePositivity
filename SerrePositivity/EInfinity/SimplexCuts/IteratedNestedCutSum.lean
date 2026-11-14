module

public import SerrePositivity.EInfinity.SimplexCuts.IteratedOuterCutSum
public import SerrePositivity.EInfinity.SimplexCuts.CochainInsertionCutDegrees
public import SerrePositivity.EInfinity.SimplexCuts.NestedGeneratorFamilies
public import SerrePositivity.EInfinity.SimplexCuts.PositiveCompositeBalancePerm

/-!
# 元の二段余作用と全二段切断の同じ有限和

Berger–Fresse §2.2.6・§3.1、M14 L12a の既存構成の法則、報告 §310。
元の二係数交換・全切断・指定生成元と面の合成を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open IntervalCuts (prefixFamily suffixFamily insertionFamily)
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma iteratedCochainAction_basis_nested_cut_sum (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (x : S _⦋q⦌) (z : ℤ)
    (hz : -(d : ℤ) + -(e : ℤ) + -(q : ℤ) = z) :
    (iteratedCochainAction A S m (n + 1) k).f z
      (ιTensorObj (Surjection.complex A (m + 1) ⊗ Surjection.complex A (n + 1)) (chains A S)
        (-(d : ℤ) + -(e : ℤ)) (-(q : ℤ)) z hz
        (ιTensorObj (Surjection.complex A (m + 1)) (Surjection.complex A (n + 1))
          (-(d : ℤ)) (-(e : ℤ)) (-(d : ℤ) + -(e : ℤ)) rfl
          ((Surjection.complexXIso A (m + 1) d).inv
            (Surjection.basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
            (Surjection.complexXIso A (n + 1) e).inv
              (Surjection.basis A (n + 1) e (ULift.up v))) ⊗ₜ[A] gen A S q x)) =
      ∑ c : PositiveNestedCutIndex u v k q, positiveNestedCutCoefficient u v k c •
        vectorTensorAt (chains A S) (m + (n + 1))
          (fun a => ⟨(positiveNestedFaceFamily u v k c a).1,
            gen A S (positiveNestedFaceFamily u v k c a).1
              (S.map (SimplexCategory.mkHom (positiveNestedFaceFamily u v k c a).2).op x)⟩) z
          (by rw [vectorDegree, positiveNested_degreeSum]
              have hn : m + n + (d + e) + q + 1 - (m + (n + 1)) = d + e + q := by omega
              rw [hn]; omega) := by
  rw [iteratedCochainAction_basis_outer_cut_sum, Fintype.sum_sigma]
  simp only [Units.smul_def, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  let f (a : Fin (m + 1)) : Σ d : ℕ, (chains A S).X (-(d : ℤ)) :=
    ⟨outputDegree s (positiveWord u) a, gen A S (outputDegree s (positiveWord u) a)
      (S.map (face s (positiveWord u) a).op x)⟩
  have hd : -(vectorDegree (chains A S) (m + 1) f : ℤ) = -(d : ℤ) + -(q : ℤ) := by
    change -(degreeSum (m + 1) (outputDegree s (positiveWord u)) : ℤ) = _
    rw [degreeSum_eq_sum, outputDegree_sum]
    have hn : m + d + q + 1 - (m + 1) = d + q := by omega
    rw [hn]; omega
  have hinner := tensorCoInsertionAction_cochain_cut_sum_at A S v k f
    (S.map (face s (positiveWord u) k).op x) rfl (-(d : ℤ) + -(q : ℤ)) z hd (by omega)
  rw [hinner]
  simp only [Units.smul_def, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro t _
  apply congrArg₂ (fun (a : ℤ) (b : (power (chains A S) (m + (n + 1))).X z) => a • b)
  · have hp : vectorDegree (chains A S) k.val (prefixFamily f k) =
        positiveNestedPrefixDegree u k s := rfl
    have hc := (positiveNestedCutCoefficient_eq_koszul u v k ⟨s, t⟩).symm
    rw [← hp] at hc
    simpa only [mul_assoc] using hc
  · apply vectorTensorAt_congr
    exact (positiveNested_vectorFamily_eq_insertion A S u v k ⟨s, t⟩ x).symm

end SerrePositivity.EInfinity.SimplexCuts
