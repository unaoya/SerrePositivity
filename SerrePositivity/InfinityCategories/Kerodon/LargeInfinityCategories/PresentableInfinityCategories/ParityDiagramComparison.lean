module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonParitySubsequences

/-!
概要：同じ全有限比較式から、元の native 全図式と指定部分列の厳密な一致を導く。
方針：全有限始区間で検出し、元の全前置面の比較式を使う。
規約：比較関手の同型へ弱めず全射の等式を保持する。使われ方：二表示の部分列比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 全有限段の元の比較式は、同じ native 図式の全部分列の等式を保証する。 -/
lemma nativeSubsequence_eq_of_finiteComparisons {I : SSet.{u}} {X : SSet.{u + 1}}
    (a : ℕ → ℕ) (ha : Monotone a) (d : ℕ → ℕ)
    (face : ∀ n, (Δ[n] : SSet.{u}) ⟶ Δ[d n])
    (hface : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex n ≫
        nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u} a ha) =
      face n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (d n))
    (J : nerve (ULift.{u} ℕ) ⟶ I) (U : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ X)
    (H : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ X)
    (Q : ∀ n, (SSet.uliftFunctor.{u + 1, u}).obj (Δ[d n] : SSet.{u}) ⟶ X)
    (R : ∀ n, (Δ[n] : SSet.{u}) ⟶ I)
    (hH : ∀ n, (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (d n)) ≫ H = Q n)
    (hJ : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex n ≫ J = R n)
    (hQR : ∀ n, (SSet.uliftFunctor.{u + 1, u}).map (face n) ≫ Q n =
      (SSet.uliftFunctor.{u + 1, u}).map (R n) ≫ U) :
    (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u} a ha)) ≫ H =
      (SSet.uliftFunctor.{u + 1, u}).map J ≫ U := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nativeSequential_hom_ext_ulift
  intro n
  calc
    _ = (SSet.uliftFunctor.{u + 1, u}).map (face n) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (d n)) ≫ H) := by
      rw [← Category.assoc, ← (SSet.uliftFunctor.{u + 1, u}).map_comp,
        hface n, (SSet.uliftFunctor.{u + 1, u}).map_comp, Category.assoc]
    _ = (SSet.uliftFunctor.{u + 1, u}).map (R n) ≫ U := by rw [hH n, hQR n]
    _ = _ := by
      rw [← Category.assoc, ← (SSet.uliftFunctor.{u + 1, u}).map_comp, hJ n]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
