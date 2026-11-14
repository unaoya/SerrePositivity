module

public import SerrePositivity.EInfinity.SimplexCuts.VectorCoInsertionActionSums
public import SerrePositivity.EInfinity.SimplexCuts.CochainActionGenerator

/-!
# 元のBF余演算の内側全切断和の代入

Berger–Fresse §2.2.6・§3.1、M14 L12a の既存構成の法則、報告 §300。
同じcochainActionの基底値を使い、内側射の評価を仮定として残さない。
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

/-- 同じcochainActionの基底値を、指定した整数全次数の全切断和で読む（BF §2.2.6）。 -/
lemma cochainAction_basis_cut_sum (A : Type u) [CommRing A] (S : SSet.{0})
    {r d q : ℕ} (u : Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌)
    (t : ℤ) (ht : -(d : ℤ) + -(q : ℤ) = t) :
    (cochainAction A S (r + 1)).f t
      (ιTensorObj (Surjection.complex A (r + 1)) (chains A S)
        (-(d : ℤ)) (-(q : ℤ)) t ht
        ((Surjection.complexXIso A (r + 1) d).inv
          (Surjection.basis A (r + 1) d (ULift.up u)) ⊗ₜ[A] gen A S q x)) =
      ∑ s : Cut (r + d) q, cutSign s (positiveWord u).val •
        vectorTensorAt (chains A S) (r + 1)
          (fun a => ⟨outputDegree s (positiveWord u) a,
            gen A S (outputDegree s (positiveWord u) a)
              (S.map (face s (positiveWord u) a).op x)⟩) t
          (by rw [vectorDegree, degreeSum_eq_sum, outputDegree_sum]
              have hnat : r + d + q + 1 - (r + 1) = d + q := by omega
              rw [hnat]; omega) := by
  have he : t = -((d + q : ℕ) : ℤ) := by omega
  subst he
  rw [cochainAction_basis_generator, cutSum_eq_sum_vectorTensorAt]

/-- 実際の内側BF余演算を指定生成元へ代入した値は、元の全切断和（BF §2.2.6・§3.1）。 -/
lemma tensorCoInsertionAction_cochain_cut_sum (A : Type u) [CommRing A] (S : SSet.{0})
    {m n e : ℕ} (v : Surjection.BasisWord (n + 1) e) (i : Fin (m + 1))
    (f : Fin (m + 1) → Σ d : ℕ, (chains A S).X (-(d : ℤ)))
    (x : S _⦋(f i).1⦌) (hx : (f i).2 = gen A S (f i).1 x) (z : ℤ)
    (hz : -(e : ℤ) + (-(vectorDegree (chains A S) i.val (prefixFamily f i) : ℤ) +
      (-((f i).1 : ℤ) + -(vectorDegree (chains A S) (m - i.val) (suffixFamily f i) : ℤ))) = z) :
    (tensorCoInsertionAction (chains A S) (Surjection.complex A (n + 1)) m (n + 1) i
      (cochainAction A S (n + 1))).f z
      (ιTensorObj (Surjection.complex A (n + 1)) (power (chains A S) (m + 1))
        (-(e : ℤ))
        (-(vectorDegree (chains A S) i.val (prefixFamily f i) : ℤ) +
          (-((f i).1 : ℤ) + -(vectorDegree (chains A S) (m - i.val) (suffixFamily f i) : ℤ)))
        z hz ((Surjection.complexXIso A (n + 1) e).inv
          (Surjection.basis A (n + 1) e (ULift.up v)) ⊗ₜ[A]
          vectorTensorAt (chains A S) (m + 1) f _
            (by have h := vectorDegree_family_blocks (chains A S) f i; omega))) =
      (-(e : ℤ) * -(vectorDegree (chains A S) i.val (prefixFamily f i) : ℤ)).negOnePow •
        ∑ s : Cut (n + e) (f i).1, cutSign s (positiveWord v).val •
          vectorTensorAt (chains A S) (m + (n + 1))
            (insertionFamily f (fun a => ⟨outputDegree s (positiveWord v) a,
              gen A S (outputDegree s (positiveWord v) a)
                (S.map (face s (positiveWord v) a).op x)⟩) i) z
            (by rw [vectorDegree_insertionFamily]
                have hs := outputDegree_sum s (positiveWord v)
                rw [← degreeSum_eq_sum] at hs
                have hnat : n + e + (f i).1 + 1 - (n + 1) = e + (f i).1 := by omega
                rw [hnat] at hs
                change -((vectorDegree (chains A S) i.val (prefixFamily f i) +
                  degreeSum (n + 1) (outputDegree s (positiveWord v)) +
                  vectorDegree (chains A S) (m - i.val) (suffixFamily f i) : ℕ) : ℤ) = z
                rw [hs]
                omega) := by
  let g (s : Cut (n + e) (f i).1) (a : Fin (n + 1)) :
      Σ d : ℕ, (chains A S).X (-(d : ℤ)) :=
    ⟨outputDegree s (positiveWord v) a, gen A S (outputDegree s (positiveWord v) a)
      (S.map (face s (positiveWord v) a).op x)⟩
  have hg (s : Cut (n + e) (f i).1) :
      -(vectorDegree (chains A S) (n + 1) (g s) : ℤ) = -(e : ℤ) + -((f i).1 : ℤ) := by
    change -(degreeSum (n + 1) (outputDegree s (positiveWord v)) : ℤ) = _
    rw [degreeSum_eq_sum, outputDegree_sum]
    have hnat : n + e + (f i).1 + 1 - (n + 1) = e + (f i).1 := by omega
    rw [hnat]
    omega
  apply tensorCoInsertionAction_vector_sum_apply (chains A S) (Surjection.complex A (n + 1))
    m (n + 1) i (cochainAction A S (n + 1)) (-(e : ℤ)) z f g hz
    ((Surjection.complexXIso A (n + 1) e).inv
      (Surjection.basis A (n + 1) e (ULift.up v))) hg (fun s => cutSign s (positiveWord v).val)
  rw [hx]
  exact cochainAction_basis_cut_sum A S v x _ rfl

end SerrePositivity.EInfinity.SimplexCuts
