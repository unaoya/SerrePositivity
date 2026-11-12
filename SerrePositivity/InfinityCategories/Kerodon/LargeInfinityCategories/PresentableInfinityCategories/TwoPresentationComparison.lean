module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonInitialParity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonSubsequenceEquality

/-!
概要：元の二つの compact filtered 表示から、同じ大域頂点上の全可算比較を構成する。
方針：指定開始点の後の実初期三角形、交互再帰、全貼合、両部分列の等式を合成する。
規約：大域頂点の compact 性と比較図式の存在を入力にしない。
使われ方：HTT 5.5.4.13 の共通小部分表示。

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


/-- 初期の全標準点の等式は、元の同じ可算添字図式の初項を回収する。 -/
lemma sequentialIndexDiagram_initial_of_point {I : SSet.{u}}
    (J : nerve (ULift.{u} ℕ) ⟶ I) (a : I _⦋0⦌)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex 0 ≫ J = SSet.yonedaEquiv.symm a) :
    J.app (Opposite.op ⦋0⦌) ((nerveEquiv (C := ULift.{u} ℕ)).symm (ULift.up 0)) = a := by
  have hp := congrArg SSet.yonedaEquiv h
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hp
  have h₀ : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex.{u} 0) =
      (nerveEquiv (C := ULift.{u} ℕ)).symm (ULift.up 0) := by
    apply ComposableArrows.ext₀
    rfl
  rw [h₀] at hp
  exact hp

/-- 元の二表示の指定開始点を保つ、共通大域頂点上の全比較と両部分列の一致。 -/
lemma exists_twoPresentationComparison
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C]
    {I₀ I₁ : SSet.{u}} [Quasicategory I₀] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I₀]
    [Quasicategory I₁] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I₁]
    (D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C)
    (D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C)
    (c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₀) (c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₁)
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (hc₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₀) (hc₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₁)
    (hD₀ : ∀ i : I₀ _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
    (hD₁ : ∀ i : I₁ _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i)))
    (hv : c₀.vertex = c₁.vertex) (a : I₀ _⦋0⦌) (b : I₁ _⦋0⦌) :
    ∃ (J₀ : nerve (ULift.{u} ℕ) ⟶ I₀) (J₁ : nerve (ULift.{u} ℕ) ⟶ I₁)
      (H : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm c₀.vertex)),
      (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n) _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingEven_monotone)) ≫ H =
          (SSet.uliftFunctor.{u + 1, u}).map J₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeSliceDiagram c₀ ∧
      (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n + 1) _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingOdd_monotone)) ≫ H =
          (SSet.uliftFunctor.{u + 1, u}).map J₁ ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transportedCoconeSliceDiagram c₁ c₀.vertex hv.symm ∧
      J₀.app (Opposite.op ⦋0⦌) ((nerveEquiv (C := ULift.{u} ℕ)).symm (ULift.up 0)) = a ∧
      ∃ j : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm b)) _⦋0⦌,
        J₁.app (Opposite.op ⦋0⦌) ((nerveEquiv (C := ULift.{u} ℕ)).symm (ULift.up 0)) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (p := SSet.yonedaEquiv.symm b) j := by
  obtain ⟨j, e, T, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactPresentations_initialTriangle D₀ D₁ c₀ c₁ hc₁ hv a b (hD₀ a)
  let b' := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (p := SSet.yonedaEquiv.symm b) j
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonInitialState c₀ c₁ hv a b' (hD₀ a) (hD₁ b') e T
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonInitialParityData c₀ c₁ hv a b' (hD₀ a) (hD₁ b') e T
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_comparisonParitySliceDiagram hμ hC hc₀ hc₁ hD₀ hD₁ s p.whole
  obtain ⟨J₀, hJ₀⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_comparisonLeftParityIndexDiagram hμ hC hc₀ hc₁ hD₀ hD₁ s p.left
  obtain ⟨J₁, hJ₁⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_comparisonRightParityIndexDiagram hμ hC hc₀ hc₁ hD₀ hD₁ s p.right
  refine ⟨J₀, J₁, H, ?_, ?_, ?_, j, ?_⟩
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparison_even_subsequence_eq hμ hC hc₀ hc₁ hD₀ hD₁ s p.whole H hH p.left p.left_face J₀ hJ₀
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparison_odd_subsequence_eq hμ hC hc₀ hc₁ hD₀ hD₁ s p.whole H hH p.right p.right_face hv.symm J₁ hJ₁
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialIndexDiagram_initial_of_point J₀ a
    have h := hJ₀ 0
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex 0 ≫ J₀ = 𝟙 _ ≫ SSet.yonedaEquiv.symm a at h
    simpa only [Category.id_comp] using h
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialIndexDiagram_initial_of_point J₁ b'
    have h := hJ₁ 0
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex 0 ≫ J₁ = 𝟙 _ ≫ SSet.yonedaEquiv.symm b' at h
    simpa only [Category.id_comp] using h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
