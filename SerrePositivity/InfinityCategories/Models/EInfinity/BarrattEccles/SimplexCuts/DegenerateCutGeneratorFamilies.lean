module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CutGeneratorFamilies
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CutTensor
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryPointNondegenerate

/-!
模型。文献の定義との比較は後で
# 退化したraw削除語から来る元の正規化零項

Berger–Fresse §2.2.6、M14 L12a、報告 §361。
元の一点削除と同じ色の埋め込みから、実際の切断の非退化性を否定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial

/-- 同じ削除後のraw語が退化なら、元の一点Cutも退化（BF §2.2.6）。 -/
lemma not_nondegenerate_of_nullary_raw_degenerate {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word (r + 1) (m + 2)) (w : Fin (m + 1) → Fin r)
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hpoint : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p)
    (hv : ∀ i, k.succAbove (w i) = v.val (p.succAbove i))
    (hw : ¬_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate w) : ¬_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate s v.val := by
  intro hcut
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.erased_word_nondegenerate_of_point_cut_nondegenerate s v p hpoint hcut
  apply hw
  intro i j hij hc
  apply he i j hij
  exact (hv i).symm.trans ((congrArg k.succAbove hc).trans (hv j))

/-- 同じ退化切断の指定次数の実生成元テンソルは零（BF §2.2.6）。 -/
lemma vectorTensorAt_cutGeneratorFamily_eq_zero (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (x : S _⦋q⦌)
    (h : ¬_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate s v.val) (z : ℤ)
    (hz : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutGeneratorFamily A S s v x) : ℤ) = z) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutGeneratorFamily A S s v x) z hz = 0 := by
  have H : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensor (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutGeneratorFamily A S s v x) = 0 := by
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTensor A S s v x = 0
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTensor_eq_zero A S s v h x
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt
  rw [H, map_zero]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
