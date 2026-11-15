module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryOutputCutSums
public import SerrePositivity.EInfinity.SimplexCuts.CutGeneratorFamilies
public import SerrePositivity.EInfinity.SimplexCuts.CochainNullaryInsertionDegrees
public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointGeneratorFamilies
public import SerrePositivity.EInfinity.SimplexCuts.ZeroFaceGenerator

/-!
# 一出現の元の全切断和と実際の空語代入の全和

Berger–Fresse §2.2.6・§3.1、M14 L12a、報告 §354。
同じ全Cut対応に元の符号・指定面・実際の余単位の値を渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial

/-- 一出現の空語代入の全和は、元の小さい全切断和（BF §2.2.6）。 -/
lemma sum_nullary_cochain_cut_terms (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (v : Surjection.Word (r + 1) (m + 2))
    (w : Surjection.Word r (m + 1)) (p : Fin (m + 2)) (k : Fin (r + 1))
    (hp : v.val p = k) (hu : ∀ j, v.val j = k → j = p)
    (hv : ∀ i, k.succAbove (w.val i) = v.val (p.succAbove i))
    (ν : Surjection.BasisWord 0 0) (x : S _⦋q⦌) (z : ℤ)
    (hz : -((m + q + 1 - r : ℕ) : ℤ) = z) :
    (∑ t : Cut m q, cutSign t w.val •
      vectorTensorAt (chains A S) r (cutGeneratorFamily A S t w x) z
        (by rw [vectorDegree_cutGeneratorFamily]; exact hz)) =
      ∑ s : Cut (m + 1) q, cutSign s v.val •
        (tensorCoInsertionAction (chains A S) (Surjection.complex A 0) r 0 k
          (cochainAction A S 0)).f z
          (ιTensorObj (Surjection.complex A 0) (power (chains A S) (r + 1)) 0 z z (zero_add z)
            ((Surjection.complexXIso A 0 0).inv (Surjection.basis A 0 0 (ULift.up ν)) ⊗ₜ[A]
              vectorTensorAt (chains A S) (r + 1) (cutGeneratorFamily A S s v x) z
                (by rw [vectorDegree_cutGeneratorFamily]
                    have h : (m + 1) + q + 1 - (r + 1) = m + q + 1 - r := by omega
                    rwa [h]))) := by
  have hu' : ∀ j, v.val j = v.val p → j = p := by
    intro j hj
    exact hu j (hj.trans hp)
  have houter (s : Cut (m + 1) q) :
      -(vectorDegree (chains A S) (r + 1) (cutGeneratorFamily A S s v x) : ℤ) = z := by
    rw [vectorDegree_cutGeneratorFamily]
    have h : (m + 1) + q + 1 - (r + 1) = m + q + 1 - r := by omega
    rwa [h]
  apply sum_nullaryOutputCuts v p k hp hu
  · intro t
    let s := nullaryPointInsertCut t p
    have hpoint : hi s p = lo s p := nullaryPointInsertCut_hi_eq_lo t p
    have hzero : outputDegree s v k = 0 :=
      (outputDegree_zero_iff_point_of_unique s v p k hp hu).mpr hpoint
    obtain ⟨y, hy⟩ := faceData_generator_zero A S
      (⟨outputDegree s v k, vertices s v k⟩ : Σ d : ℕ, Fin (d + 1) →o Fin (q + 1)) hzero x
    have hθ := tensorCoInsertionAction_cochain_nullary_zero_at A S ν k
      (cutGeneratorFamily A S s v x) y hy z z (houter s) (zero_add z)
    have hf : cutGeneratorFamily A S t w x =
        IntervalCuts.insertionFamily (cutGeneratorFamily A S s v x)
          (fun j : Fin 0 => Fin.elim0 j) k := by
      have H := nullaryPointEraseCut_generatorFamily_relabel A S s v w p k hp hpoint hv x
      change cutGeneratorFamily A S (nullaryPointEraseCut s p) w x =
        IntervalCuts.insertionFamily (cutGeneratorFamily A S s v x)
          (fun j : Fin 0 => Fin.elim0 j) k at H
      simpa only [s, nullaryPointEraseCut_insert] using H
    have hs : cutSign t w.val = cutSign s v.val := by
      have H := nullaryPointEraseCut_cutSign_relabel s v.val w.val p k hpoint hu' hv
      simpa only [s, nullaryPointEraseCut_insert] using H
    rw [hs]
    apply congrArg (fun y => cutSign s v.val • y)
    refine (vectorTensorAt_congr (chains A S) r _ _ z _ _ hf).trans hθ.symm
  · intro s hs
    have hpos : 0 < (cutGeneratorFamily A S s v x k).1 := Nat.pos_of_ne_zero hs
    have H := tensorCoInsertionAction_cochain_nullary_positive_at A S ν k
      (cutGeneratorFamily A S s v x) hpos z z (houter s) (zero_add z)
    exact (congrArg (fun y => cutSign s v.val • y) H).trans (smul_zero _)

end SerrePositivity.EInfinity.SimplexCuts
