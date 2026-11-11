module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonParityFaces
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialEvenFaceComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingOddSubsequenceComparison

/-!
概要：可算全比較の偶数・奇数部分列を、全有限前置面で厳密に検出する。
方針：可算 nerve の元の有限鎖の値を計算する。
規約：辺列だけでなく全射の等式。使われ方：元の両添字図式との部分列比較。

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


/-- 偶数部分列の全有限制限は、全比較の同じ偶数前置面である。 -/
lemma sequentialNerveInitialSimplex_comparison_even (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex.{u} n ≫
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u} (fun k ↦ 2 * k) _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingEven_monotone) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonEvenFace n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (2 * n + 1) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  exact ComposableArrows.ext (fun _ ↦ rfl) (fun _ _ ↦ Subsingleton.elim _ _)

/-- 奇数部分列の全有限制限も、全比較の同じ奇数前置面である。 -/
lemma sequentialNerveInitialSimplex_comparison_odd (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex.{u} n ≫
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u} (fun k ↦ 2 * k + 1) _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingOdd_monotone) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonOddFace n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (2 * n + 1) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  exact ComposableArrows.ext (fun _ ↦ rfl) (fun _ _ ↦ Subsingleton.elim _ _)

/-- native な可算図式の一致は、持ち上げた全有限始区間で検出できる。 -/
lemma nativeSequential_hom_ext_ulift {X : SSet.{u + 1}}
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ X}
    (h : ∀ n, (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex n) ≫ F =
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex n) ≫ G) : F = G := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nativeSequential_hom_ext
  intro n
  have hn := congrArg (fun f ↦ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} n).inv ≫ f) (h n)
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nativeSequentialInitialSimplex, Category.assoc] using hn

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
