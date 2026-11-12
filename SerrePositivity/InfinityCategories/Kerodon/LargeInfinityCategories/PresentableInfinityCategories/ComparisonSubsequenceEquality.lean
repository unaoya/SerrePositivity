module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonParityDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonSliceRestrictions
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ParityDiagramComparison

/-!
概要：元の二表示の全添字図式を、共通大域頂点上の全比較の両部分列と同定する。
方針：全有限段の偶数・奇数面の式と、元の全余錐の制限式を合わせる。
規約：全射の厳密な等式を保持する。使われ方：両側の共通小部分余極限の比較。

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

variable {μ : Cardinal.{u}} [Fact μ.IsRegular] {C : SSet.{u + 1}} [Quasicategory C]
  {I₀ I₁ : SSet.{u}}
  {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
  {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
  {c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₀} {c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₁}
variable (hμ : Cardinal.aleph0 < μ)
  [Quasicategory I₀] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I₀]
  [Quasicategory I₁] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I₁]
  (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (hc₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₀) (hc₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₁)
  (hD₀ : ∀ i : I₀ _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
  (hD₁ : ∀ i : I₁ _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i)))
  (s₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactPresentationComparison μ D₀ D₁ c₀ c₁)
  (e₀ : s₀.shape ≅ (Δ[1] : SSet.{u}))
  (H : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm c₀.vertex))
  (hH : ∀ n, (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (2 * n + 1)) ≫ H =
    (SSet.uliftFunctor.{u + 1, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSliceDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n))

include hH

/-- 共通全比較の偶数部分列は、元の左表示余錐の全添字図式そのものである。 -/
lemma comparison_even_subsequence_eq
    (l₀ : s₀.left_shape ≅ (Δ[0] : SSet.{u}))
    (h₀ : s₀.left_inclusion ≫ e₀.hom = l₀.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonEvenFace 0)
    (J : nerve (ULift.{u} ℕ) ⟶ I₀)
    (hJ : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex n ≫ J =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceLeftParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ l₀ n).inv ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).left_index) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n) _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingEven_monotone)) ≫ H =
    (SSet.uliftFunctor.{u + 1, u}).map J ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeSliceDiagram c₀ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nativeSubsequence_eq_of_finiteComparisons (fun n ↦ 2 * n) _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingEven_monotone
    (fun n ↦ 2 * n + 1) _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonEvenFace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex_comparison_even
    J (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeSliceDiagram c₀) H _ _ hH hJ
  intro n
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n
  let l := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceLeftParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ l₀ n
  have hf : s.left_inclusion ≫ e.hom = l.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonEvenFace n :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence_left_parity_face hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ l₀ h₀ n
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonEvenFace n ≫ e.inv = l.inv ≫ s.left_inclusion := by
    apply (cancel_epi l.hom).mp
    rw [← Category.assoc, ← hf, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Iso.hom_inv_id_assoc]
  change (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonEvenFace n) ≫
    ((SSet.uliftFunctor.{u + 1, u}).map e.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSliceDiagram s) =
      (SSet.uliftFunctor.{u + 1, u}).map (l.inv ≫ s.left_index) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeSliceDiagram c₀
  rw [← Category.assoc, ← (SSet.uliftFunctor.{u + 1, u}).map_comp, hi,
    (SSet.uliftFunctor.{u + 1, u}).map_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSliceDiagram_left,
    ← Category.assoc, ← (SSet.uliftFunctor.{u + 1, u}).map_comp]

/-- 奇数部分列も、共通大域頂点上へ移した元の右表示余錐の全図式に厳密に一致する。 -/
lemma comparison_odd_subsequence_eq
    (l₀ : s₀.right_shape ≅ (Δ[0] : SSet.{u}))
    (h₀ : s₀.right_inclusion ≫ e₀.hom = l₀.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonOddFace 0)
    (hz : c₁.vertex = c₀.vertex) (J : nerve (ULift.{u} ℕ) ⟶ I₁)
    (hJ : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex n ≫ J =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceRightParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ l₀ n).inv ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).right_index) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n + 1) _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingOdd_monotone)) ≫ H =
    (SSet.uliftFunctor.{u + 1, u}).map J ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transportedCoconeSliceDiagram c₁ c₀.vertex hz := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nativeSubsequence_eq_of_finiteComparisons (fun n ↦ 2 * n + 1) _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingOdd_monotone
    (fun n ↦ 2 * n + 1) _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonOddFace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex_comparison_odd
    J (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transportedCoconeSliceDiagram c₁ c₀.vertex hz) H _ _ hH hJ
  intro n
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n
  let l := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceRightParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ l₀ n
  have hf : s.right_inclusion ≫ e.hom = l.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonOddFace n :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence_right_parity_face hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ l₀ h₀ n
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonOddFace n ≫ e.inv = l.inv ≫ s.right_inclusion := by
    apply (cancel_epi l.hom).mp
    rw [← Category.assoc, ← hf, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Iso.hom_inv_id_assoc]
  change (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonOddFace n) ≫
    ((SSet.uliftFunctor.{u + 1, u}).map e.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSliceDiagram s) =
      (SSet.uliftFunctor.{u + 1, u}).map (l.inv ≫ s.right_index) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transportedCoconeSliceDiagram c₁ c₀.vertex hz
  rw [← Category.assoc, ← (SSet.uliftFunctor.{u + 1, u}).map_comp, hi,
    (SSet.uliftFunctor.{u + 1, u}).map_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSliceDiagram_right s hz,
    ← Category.assoc, ← (SSet.uliftFunctor.{u + 1, u}).map_comp]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
