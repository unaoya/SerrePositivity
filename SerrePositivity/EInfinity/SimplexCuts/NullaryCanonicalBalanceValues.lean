module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryCanonicalBalanceTerms

/-!
# 元の空語Cut対合の対応項と固定零項の値

Berger–Fresse §2.2.6、M14 L12a、報告 §372。
元の一点挿入・指定面・整数符号・実際の余単位の評価をそのまま使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial

/-- 元の一点挿入に対応する二つの実際のCut項は一致（BF §2.2.6）。 -/
lemma nullarySmallCutTerm_eq_insert (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (v : Surjection.Word (r + 1) (m + 2)) (w : Surjection.Word r (m + 1))
    (ν : Surjection.BasisWord 0 0) (p : Fin (m + 2)) (k : Fin (r + 1))
    (hp : v.val p = k) (hu : ∀ j, v.val j = k → j = p)
    (hv : ∀ i, k.succAbove (w.val i) = v.val (p.succAbove i))
    (x : S _⦋q⦌) (z : ℤ) (hz : -((m + q + 1 - r : ℕ) : ℤ) = z) (t : Cut m q) :
    nullarySmallCutTerm A S w x z hz t =
      nullaryOuterCutTerm A S v ν k x z hz (nullaryPointInsertCut t p) := by
  unfold nullarySmallCutTerm nullaryOuterCutTerm
  let s := nullaryPointInsertCut t p
  have hpoint : hi s p = lo s p := nullaryPointInsertCut_hi_eq_lo t p
  have hzero : outputDegree s v k = 0 :=
    (outputDegree_zero_iff_point_of_unique s v p k hp hu).mpr hpoint
  have houter : -(vectorDegree (chains A S) (r + 1) (cutGeneratorFamily A S s v x) : ℤ) = z := by
    rw [vectorDegree_cutGeneratorFamily]
    have h : (m + 1) + q + 1 - (r + 1) = m + q + 1 - r := by omega
    rwa [h]
  obtain ⟨y, hy⟩ := faceData_generator_zero A S
    (⟨outputDegree s v k, vertices s v k⟩ : Σ d : ℕ, Fin (d + 1) →o Fin (q + 1)) hzero x
  have hθ := tensorCoInsertionAction_cochain_nullary_zero_at A S ν k
    (cutGeneratorFamily A S s v x) y hy z z houter (zero_add z)
  have hf : cutGeneratorFamily A S t w x =
      IntervalCuts.insertionFamily (cutGeneratorFamily A S s v x)
        (fun j : Fin 0 => Fin.elim0 j) k := by
    have H := nullaryPointEraseCut_generatorFamily_relabel A S s v w p k hp hpoint hv x
    change cutGeneratorFamily A S (nullaryPointEraseCut s p) w x =
      IntervalCuts.insertionFamily (cutGeneratorFamily A S s v x)
        (fun j : Fin 0 => Fin.elim0 j) k at H
    simpa only [s, nullaryPointEraseCut_insert] using H
  have hu' : ∀ j, v.val j = v.val p → j = p := fun j hj => hu j (hj.trans hp)
  have hs : cutSign t w.val = cutSign s v.val := by
    have H := nullaryPointEraseCut_cutSign_relabel s v.val w.val p k hpoint hu' hv
    simpa only [s, nullaryPointEraseCut_insert] using H
  rw [hs]
  apply congrArg (fun y => cutSign s v.val • y)
  exact (vectorTensorAt_congr (chains A S) r _ _ z _ _ hf).trans hθ.symm

/-- 元の右の正次数Cut項は実際の空語作用で零（BF §2.2.6）。 -/
lemma nullaryOuterCutTerm_eq_zero_of_nonzero (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (v : Surjection.Word (r + 1) (m + 2)) (ν : Surjection.BasisWord 0 0)
    (k : Fin (r + 1)) (x : S _⦋q⦌) (z : ℤ) (hz : -((m + q + 1 - r : ℕ) : ℤ) = z)
    (s : Cut (m + 1) q) (hs : outputDegree s v k ≠ 0) :
    nullaryOuterCutTerm A S v ν k x z hz s = 0 := by
  unfold nullaryOuterCutTerm
  have houter : -(vectorDegree (chains A S) (r + 1) (cutGeneratorFamily A S s v x) : ℤ) = z := by
    rw [vectorDegree_cutGeneratorFamily]
    have h : (m + 1) + q + 1 - (r + 1) = m + q + 1 - r := by omega
    rwa [h]
  have hpos : 0 < (cutGeneratorFamily A S s v x k).1 := Nat.pos_of_ne_zero hs
  have H := tensorCoInsertionAction_cochain_nullary_positive_at A S ν k
    (cutGeneratorFamily A S s v x) hpos z z houter (zero_add z)
  exact (congrArg (fun y => cutSign s v.val • y) H).trans (smul_zero _)

end SerrePositivity.EInfinity.SimplexCuts
