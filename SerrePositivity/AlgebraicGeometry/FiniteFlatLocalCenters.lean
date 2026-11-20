module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.FreeCoverCharts
public import SerrePositivity.AlgebraicGeometry.ChartLocalFlattening

/-!
概要：KST §5、Stacks 0815 の境界外で平坦な有限加群に対する有限チャート族の局所平坦化中心。
方針：分子中心を選んで境界外を自由にし、各生成元チャート上で局所中心を選ぶ。
規約：この定理では局所中心をまだ大域の一つの中心にはまとめない。
使われ方：中心の延長・共通細分・二段合成の支配による大域平坦化。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R M N : Type*} [CommRing R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]
  [AddCommGroup N] [Module R N]

set_option maxHeartbeats 1000000 in
-- 二段のチャート環と局所化加群のインスタンスの照合が既定の上限を超えるため。
set_option backward.isDefEq.respectTransparency false in
/--
概要：境界外で平坦な有限加群に最初の中心と有限チャート上の実際の局所平坦化中心が存在。
方針：局所化先の有限表示性を導き、分子中心の各チャートに自由境界の平坦化を適用する。
規約：KST §5、Stacks 0815、二段目の中心はチャート環のイデアルとして返す。
使われ方：局所中心を一つの admissible blowup へまとめる段階の入力。
-/
theorem exists_noetherian_finite_local_flattening_centers
    (f : R) (hf : f ∈ nonZeroDivisors R)
    [Module (Localization.Away f) N] [IsScalarTower R (Localization.Away f) N]
    (μ : M →ₗ[R] N) [IsLocalizedModule.Away f μ] [Module.Flat (Localization.Away f) N] :
    ∃ s : Finset (Localization.Away f), (freeCoverNumeratorIdeal f s).FG ∧
      PrimeSpectrum.basicOpen f ≤ affineCenterComplement (freeCoverNumeratorIdeal f s) ∧
      ∀ i : s,
        let I := freeCoverNumeratorIdeal f s
        let a := freeCoverNumeratorGenerator f s i
        let A := BlowupChartRing I a
        letI : Algebra R A := (chartBaseMap I a).toAlgebra
        ∃ K : Ideal A, K.FG ∧
          PrimeSpectrum.basicOpen (chartBaseMap I a f) ≤ affineCenterComplement K ∧
          ∀ b : K, letI : Algebra A (BlowupChartRing K b) := (chartBaseMap K b).toAlgebra
            Module.Flat (BlowupChartRing K b)
              (modulePureTransform (chartBaseMap K b (chartBaseMap I a f))
                (BlowupChartRing K b ⊗[A] (A ⊗[R] M))) := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  let L := Localization.Away f
  let eμ := (IsLocalizedModule.isBaseChange (Submonoid.powers f) L μ).equiv
  have : Module.FinitePresentation L N := Module.FinitePresentation.of_equiv eμ
  with_reducible_and_instances
    obtain ⟨s, hfg, hU, hfree⟩ := exists_initialFreeBoundary_center (M := M) (N := N) f μ
    refine ⟨s, hfg, hU, ?_⟩
    intro i
    exact exists_chart_flattening_center
      (freeCoverNumeratorIdeal f s) (freeCoverNumeratorGenerator f s i) f M hf (hfree i)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
