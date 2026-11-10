module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonParityDiagrams
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonSliceRestrictions
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ParityDiagramComparison

/-!
概要：元の二表示の全添字図式を、共通大域頂点上の全比較の両部分列と同定する。
方針：全有限段の偶数・奇数面の式と、元の全余錐の制限式を合わせる。
規約：全射の厳密な等式を保持する。使われ方：両側の共通小部分余極限の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact
variable {μ : Cardinal.{u}} [Fact μ.IsRegular] {C : SSet.{u + 1}} [Quasicategory C]
  {I₀ I₁ : SSet.{u}}
  {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
  {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
  {c₀ : JoinCocone D₀} {c₁ : JoinCocone D₁}
variable (hμ : Cardinal.aleph0 < μ)
  [Quasicategory I₀] [IsKappaFiltered μ I₀]
  [Quasicategory I₁] [IsKappaFiltered μ I₁]
  (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (hc₀ : IsColimitCone c₀) (hc₁ : IsColimitCone c₁)
  (hD₀ : ∀ i : I₀ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
  (hD₁ : ∀ i : I₁ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i)))
  (s₀ : CompactPresentationComparison μ D₀ D₁ c₀ c₁)
  (e₀ : s₀.shape ≅ (Δ[1] : SSet.{u}))
  (H : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶
    sliceOver (SSet.yonedaEquiv.symm c₀.vertex))
  (hH : ∀ n, (SSet.uliftFunctor.{u + 1, u}).map (sequentialNerveInitialSimplex (2 * n + 1)) ≫ H =
    (SSet.uliftFunctor.{u + 1, u}).map
      (comparisonSequenceParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n).inv ≫
        comparisonSliceDiagram (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n))

include hH

/-- 共通全比較の偶数部分列は、元の左表示余錐の全添字図式そのものである。 -/
lemma comparison_even_subsequence_eq
    (l₀ : s₀.left_shape ≅ (Δ[0] : SSet.{u}))
    (h₀ : s₀.left_inclusion ≫ e₀.hom = l₀.hom ≫ comparisonEvenFace 0)
    (J : nerve (ULift.{u} ℕ) ⟶ I₀)
    (hJ : ∀ n, sequentialNerveInitialSimplex n ≫ J =
      (comparisonSequenceLeftParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ l₀ n).inv ≫
        (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).left_index) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n) alternatingEven_monotone)) ≫ H =
    (SSet.uliftFunctor.{u + 1, u}).map J ≫ coconeSliceDiagram c₀ := by
  apply nativeSubsequence_eq_of_finiteComparisons (fun n ↦ 2 * n) alternatingEven_monotone
    (fun n ↦ 2 * n + 1) comparisonEvenFace sequentialNerveInitialSimplex_comparison_even
    J (coconeSliceDiagram c₀) H _ _ hH hJ
  intro n
  let s := comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n
  let e := comparisonSequenceParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n
  let l := comparisonSequenceLeftParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ l₀ n
  have hf : s.left_inclusion ≫ e.hom = l.hom ≫ comparisonEvenFace n :=
    comparisonSequence_left_parity_face hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ l₀ h₀ n
  have hi : comparisonEvenFace n ≫ e.inv = l.inv ≫ s.left_inclusion := by
    apply (cancel_epi l.hom).mp
    rw [← Category.assoc, ← hf, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Iso.hom_inv_id_assoc]
  change (SSet.uliftFunctor.{u + 1, u}).map (comparisonEvenFace n) ≫
    ((SSet.uliftFunctor.{u + 1, u}).map e.inv ≫ comparisonSliceDiagram s) =
      (SSet.uliftFunctor.{u + 1, u}).map (l.inv ≫ s.left_index) ≫ coconeSliceDiagram c₀
  rw [← Category.assoc, ← (SSet.uliftFunctor.{u + 1, u}).map_comp, hi,
    (SSet.uliftFunctor.{u + 1, u}).map_comp, Category.assoc, comparisonSliceDiagram_left,
    ← Category.assoc, ← (SSet.uliftFunctor.{u + 1, u}).map_comp]

/-- 奇数部分列も、共通大域頂点上へ移した元の右表示余錐の全図式に厳密に一致する。 -/
lemma comparison_odd_subsequence_eq
    (l₀ : s₀.right_shape ≅ (Δ[0] : SSet.{u}))
    (h₀ : s₀.right_inclusion ≫ e₀.hom = l₀.hom ≫ comparisonOddFace 0)
    (hz : c₁.vertex = c₀.vertex) (J : nerve (ULift.{u} ℕ) ⟶ I₁)
    (hJ : ∀ n, sequentialNerveInitialSimplex n ≫ J =
      (comparisonSequenceRightParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ l₀ n).inv ≫
        (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).right_index) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n + 1) alternatingOdd_monotone)) ≫ H =
    (SSet.uliftFunctor.{u + 1, u}).map J ≫ transportedCoconeSliceDiagram c₁ c₀.vertex hz := by
  apply nativeSubsequence_eq_of_finiteComparisons (fun n ↦ 2 * n + 1) alternatingOdd_monotone
    (fun n ↦ 2 * n + 1) comparisonOddFace sequentialNerveInitialSimplex_comparison_odd
    J (transportedCoconeSliceDiagram c₁ c₀.vertex hz) H _ _ hH hJ
  intro n
  let s := comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n
  let e := comparisonSequenceParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n
  let l := comparisonSequenceRightParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ l₀ n
  have hf : s.right_inclusion ≫ e.hom = l.hom ≫ comparisonOddFace n :=
    comparisonSequence_right_parity_face hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ l₀ h₀ n
  have hi : comparisonOddFace n ≫ e.inv = l.inv ≫ s.right_inclusion := by
    apply (cancel_epi l.hom).mp
    rw [← Category.assoc, ← hf, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Iso.hom_inv_id_assoc]
  change (SSet.uliftFunctor.{u + 1, u}).map (comparisonOddFace n) ≫
    ((SSet.uliftFunctor.{u + 1, u}).map e.inv ≫ comparisonSliceDiagram s) =
      (SSet.uliftFunctor.{u + 1, u}).map (l.inv ≫ s.right_index) ≫
        transportedCoconeSliceDiagram c₁ c₀.vertex hz
  rw [← Category.assoc, ← (SSet.uliftFunctor.{u + 1, u}).map_comp, hi,
    (SSet.uliftFunctor.{u + 1, u}).map_comp, Category.assoc, comparisonSliceDiagram_right s hz,
    ← Category.assoc, ← (SSet.uliftFunctor.{u + 1, u}).map_comp]

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
