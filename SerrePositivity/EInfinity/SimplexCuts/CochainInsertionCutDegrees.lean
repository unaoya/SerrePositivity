module

public import SerrePositivity.EInfinity.SimplexCuts.CochainInsertionCutSum

/-!
# 指定した入力次数での元の内側切断和

Berger–Fresse §2.2.6・§3.1、M14 L12a の既存構成の法則、報告 §309。
同じ指定入力次数・生成元・有限族を保つ。
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

/-- 元の入力次数を指定しても、同じ内側全切断和で評価する（BF §2.2.6）。 -/
lemma tensorCoInsertionAction_cochain_cut_sum_at (A : Type u) [CommRing A] (S : SSet.{0})
    {m n e : ℕ} (v : Surjection.BasisWord (n + 1) e) (i : Fin (m + 1))
    (f : Fin (m + 1) → Σ d : ℕ, (chains A S).X (-(d : ℤ)))
    (x : S _⦋(f i).1⦌) (hx : (f i).2 = gen A S (f i).1 x) (p z : ℤ)
    (hp : -(vectorDegree (chains A S) (m + 1) f : ℤ) = p)
    (hz : -(e : ℤ) + p = z) :
    (tensorCoInsertionAction (chains A S) (Surjection.complex A (n + 1)) m (n + 1) i
      (cochainAction A S (n + 1))).f z
      (ιTensorObj (Surjection.complex A (n + 1)) (power (chains A S) (m + 1))
        (-(e : ℤ))
        p
        z hz ((Surjection.complexXIso A (n + 1) e).inv
          (Surjection.basis A (n + 1) e (ULift.up v)) ⊗ₜ[A]
          vectorTensorAt (chains A S) (m + 1) f p hp)) =
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
                have hf := vectorDegree_family_blocks (chains A S) f i
                omega) := by
  have he : p = -(vectorDegree (chains A S) i.val (prefixFamily f i) : ℤ) +
      (-((f i).1 : ℤ) + -(vectorDegree (chains A S) (m - i.val) (suffixFamily f i) : ℤ)) := by
    have hf := vectorDegree_family_blocks (chains A S) f i
    omega
  subst he
  exact tensorCoInsertionAction_cochain_cut_sum A S v i f x hx z hz

end SerrePositivity.EInfinity.SimplexCuts
