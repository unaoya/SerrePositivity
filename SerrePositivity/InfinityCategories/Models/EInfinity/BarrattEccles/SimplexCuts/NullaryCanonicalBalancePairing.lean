module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryCanonicalBalanceValues

/-!
模型。文献の定義との比較は後で
# 元の空語の全Cutを零項ごと保持する対合

Berger–Fresse §2.2.6、M14 L12a、報告 §372。
同じ元の一点Cut同値を全ての係数環・入力単体に共通の対合へ包装する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial

/-- 同じ全Cutの対合は、全係数環・入力に共通に固定零項と相殺項を与える（BF §2.2.6）。 -/
lemma nullaryCanonicalBalance_pairing {m q r : ℕ}
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word (r + 1) (m + 2)) (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1))
    (ν : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (p : Fin (m + 2)) (k : Fin (r + 1))
    (hp : v.val p = k) (hu : ∀ j, v.val j = k → j = p)
    (hv : ∀ i, k.succAbove (w.val i) = v.val (p.succAbove i)) :
    ∃ τ : Equiv.Perm (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q ⊕ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q), Function.Involutive τ ∧
      (∀ i, τ i = i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌) (z : ℤ)
        (hz : -((m + q + 1 - r : ℕ) : ℤ) = z),
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryCanonicalBalanceTerm A S v w ν k x z hz i = 0) ∧
      (∀ i, τ i ≠ i → ∀ (A : Type u) [CommRing A] (S : SSet.{0}) (x : S _⦋q⦌) (z : ℤ)
        (hz : -((m + q + 1 - r : ℕ) : ℤ) = z),
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryCanonicalBalanceTerm A S v w ν k x z hz (τ i) =
          -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryCanonicalBalanceTerm A S v w ν k x z hz i) := by
  let P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q → Prop := fun s => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s v k = 0
  let e := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryOutputCutEquiv m q (r + 1) v p k hp hu
  refine ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryCanonicalBalancePerm v p k hp hu, ?_, ?_, ?_⟩
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.matchedSubsetExchange_involutive P e
  · intro i hi A hA S x z hz
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.matchedSubsetPerm_fixed_zero P e
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullarySmallCutTerm A S w x z hz) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryOuterCutTerm A S v ν k x z hz)
      (fun s hs => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryOuterCutTerm_eq_zero_of_nonzero A S v ν k x z hz s hs) i hi
  · intro i _ A hA S x z hz
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.matchedSubsetPerm_term_neg P e
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullarySmallCutTerm A S w x z hz) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryOuterCutTerm A S v ν k x z hz)
      (fun t => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullarySmallCutTerm_eq_insert A S v w ν p k hp hu hv x z hz t)
      (fun s hs => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryOuterCutTerm_eq_zero_of_nonzero A S v ν k x z hz s hs) i

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
