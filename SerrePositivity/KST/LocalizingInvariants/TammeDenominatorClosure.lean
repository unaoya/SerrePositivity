module

public import SerrePositivity.KST.LocalizingInvariants.TammeQuotientCandidate
public import SerrePositivity.InfinityCategories.Stable.Exact.ExactKernelStableClosure
public import SerrePositivity.InfinityCategories.Stable.CofiberLocalizingBaseChange
public import SerrePositivity.InfinityCategories.Stable.CofiberLocalizingComposition

/-!
概要：元の Tamme 分母の集合は普遍 pullback・pushout に沿って閉じ、二対三性を持つ。
方針：元の核の安定閉包との一致を証明し、既存の実 cofiber 分母計算を同じ集合へ移す。
規約：指定した実四角形と二単体を保持。使われ方：coherent 分数と有限図式の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

lemma tammeKernel_stableClosure :
    {x | StableVertexClosure (essentialImage (pullbackInclusion p q)) x} =
      essentialImage (pullbackInclusion p q) :=
  stableClosure_eq_of_exact_kernel _ _ (exactLaxDifference_kernel p q)

lemma tammeLocalizingEdges_stableClosure :
    cofiberLocalizingEdges {x | StableVertexClosure (essentialImage (pullbackInclusion p q)) x} =
      tammeLocalizingEdges p q := by
  rw [tammeKernel_stableClosure]
  rfl

lemma tammeLocalizingEdges_pushout_iff
    (s : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (laxCategory p q).obj) (hs : IsPushoutSquare s) :
    (squareLeftArrow s).edge ∈ tammeLocalizingEdges p q ↔
      (squareRightArrow s).edge ∈ tammeLocalizingEdges p q := by
  simpa only [tammeLocalizingEdges_stableClosure] using
    cofiberStableEdges_pushout_iff (essentialImage (pullbackInclusion p q)) s hs

lemma tammeLocalizingEdges_pullback_iff
    (s : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (laxCategory p q).obj) (hs : IsPullbackSquare s) :
    (squareLeftArrow s).edge ∈ tammeLocalizingEdges p q ↔
      (squareRightArrow s).edge ∈ tammeLocalizingEdges p q := by
  simpa only [tammeLocalizingEdges_stableClosure] using
    cofiberStableEdges_pullback_iff (essentialImage (pullbackInclusion p q)) s hs

lemma tammeLocalizingEdges_twoOfThree (τ : (Δ[2] : SSet.{u}) ⟶ (laxCategory p q).obj) :
    let W := fun i : Fin 3 => SSet.yonedaEquiv (stdSimplex.δ i ≫ τ) ∈ tammeLocalizingEdges p q
    (W 2 → W 0 → W 1) ∧ (W 2 → W 1 → W 0) ∧ (W 0 → W 1 → W 2) := by
  simpa only [tammeLocalizingEdges_stableClosure] using
    cofiberStableEdges_twoOfThree (essentialImage (pullbackInclusion p q)) τ

lemma tammeLocalizingEdges_of_isInvertible {a : (laxCategory p q).obj _⦋1⦌}
    (ha : IsInvertibleEdge (edgeOfSimplex a)) : a ∈ tammeLocalizingEdges p q := by
  rw [← tammeLocalizingEdges_stableClosure]
  exact cofiberStableEdges_of_isInvertible _ ha

end SerrePositivity.KST.LocalizingInvariants
