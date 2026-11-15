module

public import SerrePositivity.EInfinity.SimplexCuts.CutGeneratorFamilies
public import SerrePositivity.EInfinity.SimplexCuts.CutTensor
public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointNondegenerate

/-!
# 退化したraw削除語から来る元の正規化零項

Berger–Fresse §2.2.6、M14 L12a、報告 §361。
元の一点削除と同じ色の埋め込みから、実際の切断の非退化性を否定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open SerrePositivity.TensorPowers
open scoped Simplicial

/-- 同じ削除後のraw語が退化なら、元の一点Cutも退化（BF §2.2.6）。 -/
lemma not_nondegenerate_of_nullary_raw_degenerate {m q r : ℕ} (s : Cut (m + 1) q)
    (v : Surjection.Word (r + 1) (m + 2)) (w : Fin (m + 1) → Fin r)
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hpoint : hi s p = lo s p)
    (hv : ∀ i, k.succAbove (w i) = v.val (p.succAbove i))
    (hw : ¬Surjection.Nondegenerate w) : ¬Nondegenerate s v.val := by
  intro hcut
  have he := erased_word_nondegenerate_of_point_cut_nondegenerate s v p hpoint hcut
  apply hw
  intro i j hij hc
  apply he i j hij
  exact (hv i).symm.trans ((congrArg k.succAbove hc).trans (hv j))

/-- 同じ退化切断の指定次数の実生成元テンソルは零（BF §2.2.6）。 -/
lemma vectorTensorAt_cutGeneratorFamily_eq_zero (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1)) (x : S _⦋q⦌)
    (h : ¬Nondegenerate s v.val) (z : ℤ)
    (hz : -(vectorDegree (chains A S) r (cutGeneratorFamily A S s v x) : ℤ) = z) :
    vectorTensorAt (chains A S) r (cutGeneratorFamily A S s v x) z hz = 0 := by
  have H : vectorTensor (chains A S) r (cutGeneratorFamily A S s v x) = 0 := by
    change cutTensor A S s v x = 0
    exact cutTensor_eq_zero A S s v h x
  unfold vectorTensorAt
  rw [H, map_zero]

end SerrePositivity.EInfinity.SimplexCuts
