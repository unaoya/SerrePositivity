module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryCanonicalBalanceTerms

/-!
模型。文献の定義との比較は後で
# 元の空語Cut対合の対応項と固定零項の値

Berger–Fresse §2.2.6、M14 L12a、報告 §372。
元の一点挿入・指定面・整数符号・実際の余単位の評価をそのまま使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial

/-- 元の一点挿入に対応する二つの実際のCut項は一致（BF §2.2.6）。 -/
lemma nullarySmallCutTerm_eq_insert (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word (r + 1) (m + 2)) (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1))
    (ν : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (p : Fin (m + 2)) (k : Fin (r + 1))
    (hp : v.val p = k) (hu : ∀ j, v.val j = k → j = p)
    (hv : ∀ i, k.succAbove (w.val i) = v.val (p.succAbove i))
    (x : S _⦋q⦌) (z : ℤ) (hz : -((m + q + 1 - r : ℕ) : ℤ) = z) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullarySmallCutTerm A S w x z hz t =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryOuterCutTerm A S v ν k x z hz (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointInsertCut t p) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullarySmallCutTerm _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryOuterCutTerm
  let s := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointInsertCut t p
  have hpoint : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointInsertCut_hi_eq_lo t p
  have hzero : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v k = 0 :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_zero_iff_point_of_unique s v p k hp hu).mpr hpoint
  have houter : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutGeneratorFamily A S s v x) : ℤ) = z := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_cutGeneratorFamily]
    have h : (m + 1) + q + 1 - (r + 1) = m + q + 1 - r := by omega
    rwa [h]
  obtain ⟨y, hy⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.faceData_generator_zero A S
    (⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v k, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices s v k⟩ : Σ d : ℕ, Fin (d + 1) →o Fin (q + 1)) hzero x
  have hθ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorCoInsertionAction_cochain_nullary_zero_at A S ν k
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutGeneratorFamily A S s v x) y hy z z houter (zero_add z)
  have hf : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutGeneratorFamily A S t w x =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.insertionFamily (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutGeneratorFamily A S s v x)
        (fun j : Fin 0 => Fin.elim0 j) k := by
    have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut_generatorFamily_relabel A S s v w p k hp hpoint hv x
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutGeneratorFamily A S (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut s p) w x =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.insertionFamily (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutGeneratorFamily A S s v x)
        (fun j : Fin 0 => Fin.elim0 j) k at H
    simpa only [s, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut_insert] using H
  have hu' : ∀ j, v.val j = v.val p → j = p := fun j hj => hu j (hj.trans hp)
  have hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSign t w.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSign s v.val := by
    have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut_cutSign_relabel s v.val w.val p k hpoint hu' hv
    simpa only [s, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryPointEraseCut_insert] using H
  rw [hs]
  apply congrArg (fun y => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSign s v.val • y)
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_congr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r _ _ z _ _ hf).trans hθ.symm

/-- 元の右の正次数Cut項は実際の空語作用で零（BF §2.2.6）。 -/
lemma nullaryOuterCutTerm_eq_zero_of_nonzero (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word (r + 1) (m + 2)) (ν : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0)
    (k : Fin (r + 1)) (x : S _⦋q⦌) (z : ℤ) (hz : -((m + q + 1 - r : ℕ) : ℤ) = z)
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q) (hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v k ≠ 0) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryOuterCutTerm A S v ν k x z hz s = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryOuterCutTerm
  have houter : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutGeneratorFamily A S s v x) : ℤ) = z := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_cutGeneratorFamily]
    have h : (m + 1) + q + 1 - (r + 1) = m + q + 1 - r := by omega
    rwa [h]
  have hpos : 0 < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutGeneratorFamily A S s v x k).1 := Nat.pos_of_ne_zero hs
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorCoInsertionAction_cochain_nullary_positive_at A S ν k
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutGeneratorFamily A S s v x) hpos z z houter (zero_add z)
  exact (congrArg (fun y => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSign s v.val • y) H).trans (smul_zero _)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
