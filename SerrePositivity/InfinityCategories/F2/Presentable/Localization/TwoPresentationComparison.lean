module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonInitialParity
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonSubsequenceEquality

/-!
概要：元の二つの compact filtered 表示から、同じ大域頂点上の全可算比較を構成する。
方針：指定開始点の後の実初期三角形、交互再帰、全貼合、両部分列の等式を合成する。
規約：大域頂点の compact 性と比較図式の存在を入力にしない。
使われ方：HTT 5.5.4.13 の共通小部分表示。
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

/-- 初期の全標準点の等式は、元の同じ可算添字図式の初項を回収する。 -/
lemma sequentialIndexDiagram_initial_of_point {I : SSet.{u}}
    (J : nerve (ULift.{u} ℕ) ⟶ I) (a : I _⦋0⦌)
    (h : sequentialNerveInitialSimplex 0 ≫ J = SSet.yonedaEquiv.symm a) :
    J.app (Opposite.op ⦋0⦌) ((nerveEquiv (C := ULift.{u} ℕ)).symm (ULift.up 0)) = a := by
  have hp := congrArg SSet.yonedaEquiv h
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hp
  have h₀ : SSet.yonedaEquiv (sequentialNerveInitialSimplex.{u} 0) =
      (nerveEquiv (C := ULift.{u} ℕ)).symm (ULift.up 0) := by
    apply ComposableArrows.ext₀
    rfl
  rw [h₀] at hp
  exact hp

/-- 元の二表示の指定開始点を保つ、共通大域頂点上の全比較と両部分列の一致。 -/
lemma exists_twoPresentationComparison
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C]
    {I₀ I₁ : SSet.{u}} [Quasicategory I₀] [IsKappaFiltered μ I₀]
    [Quasicategory I₁] [IsKappaFiltered μ I₁]
    (D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C)
    (D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C)
    (c₀ : JoinCocone D₀) (c₁ : JoinCocone D₁)
    (hC : HasSmallColimits C) (hc₀ : IsColimitCone c₀) (hc₁ : IsColimitCone c₁)
    (hD₀ : ∀ i : I₀ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
    (hD₁ : ∀ i : I₁ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i)))
    (hv : c₀.vertex = c₁.vertex) (a : I₀ _⦋0⦌) (b : I₁ _⦋0⦌) :
    ∃ (J₀ : nerve (ULift.{u} ℕ) ⟶ I₀) (J₁ : nerve (ULift.{u} ℕ) ⟶ I₁)
      (H : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶
        sliceOver (SSet.yonedaEquiv.symm c₀.vertex)),
      (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n) alternatingEven_monotone)) ≫ H =
          (SSet.uliftFunctor.{u + 1, u}).map J₀ ≫ coconeSliceDiagram c₀ ∧
      (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n + 1) alternatingOdd_monotone)) ≫ H =
          (SSet.uliftFunctor.{u + 1, u}).map J₁ ≫
            transportedCoconeSliceDiagram c₁ c₀.vertex hv.symm ∧
      J₀.app (Opposite.op ⦋0⦌) ((nerveEquiv (C := ULift.{u} ℕ)).symm (ULift.up 0)) = a ∧
      ∃ j : (sliceUnder (SSet.yonedaEquiv.symm b)) _⦋0⦌,
        J₁.app (Opposite.op ⦋0⦌) ((nerveEquiv (C := ULift.{u} ℕ)).symm (ULift.up 0)) =
          JoinCocone.vertex (p := SSet.yonedaEquiv.symm b) j := by
  obtain ⟨j, e, T, _⟩ := compactPresentations_initialTriangle D₀ D₁ c₀ c₁ hc₁ hv a b (hD₀ a)
  let b' := JoinCocone.vertex (p := SSet.yonedaEquiv.symm b) j
  let s := comparisonInitialState c₀ c₁ hv a b' (hD₀ a) (hD₁ b') e T
  let p := comparisonInitialParityData c₀ c₁ hv a b' (hD₀ a) (hD₁ b') e T
  obtain ⟨H, hH⟩ := exists_comparisonParitySliceDiagram hμ hC hc₀ hc₁ hD₀ hD₁ s p.whole
  obtain ⟨J₀, hJ₀⟩ := exists_comparisonLeftParityIndexDiagram hμ hC hc₀ hc₁ hD₀ hD₁ s p.left
  obtain ⟨J₁, hJ₁⟩ := exists_comparisonRightParityIndexDiagram hμ hC hc₀ hc₁ hD₀ hD₁ s p.right
  refine ⟨J₀, J₁, H, ?_, ?_, ?_, j, ?_⟩
  · exact comparison_even_subsequence_eq hμ hC hc₀ hc₁ hD₀ hD₁ s p.whole H hH p.left p.left_face J₀ hJ₀
  · exact comparison_odd_subsequence_eq hμ hC hc₀ hc₁ hD₀ hD₁ s p.whole H hH p.right p.right_face hv.symm J₁ hJ₁
  · apply sequentialIndexDiagram_initial_of_point J₀ a
    have h := hJ₀ 0
    change sequentialNerveInitialSimplex 0 ≫ J₀ = 𝟙 _ ≫ SSet.yonedaEquiv.symm a at h
    simpa only [Category.id_comp] using h
  · apply sequentialIndexDiagram_initial_of_point J₁ b'
    have h := hJ₁ 0
    change sequentialNerveInitialSimplex 0 ≫ J₁ = 𝟙 _ ≫ SSet.yonedaEquiv.symm b' at h
    simpa only [Category.id_comp] using h

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
