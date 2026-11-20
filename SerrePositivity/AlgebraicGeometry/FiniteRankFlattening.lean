module

public import SerrePositivity.AlgebraicGeometry.FiniteRankIsogeny
public import SerrePositivity.AlgebraicGeometry.DeterminantalChartImage
public import SerrePositivity.AlgebraicGeometry.IdealFlattening

/-!
概要：KST §5、Stacks 0815 の境界外で有限階数自由な有限加群の行列式平坦化中心。
方針：分母倍の両射から行列式中心を作り、その生成元チャートの被覆上で純変換を自由化する。
規約：Noether 環上の有限加群を対象とし、一般の有限型代数上の有限加群とは区別する。
使われ方：一般チャートへの平坦性の移送と加群の平坦化の準備。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R M M' ι : Type*} [CommRing R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]
  [AddCommGroup M'] [Module R M'] [Fintype ι] [DecidableEq ι]

/--
概要：境界外で有限階数自由な有限加群に、生成元チャート上で純変換を平坦にする実際の中心が存在。
方針：像の全列行列の行列式中心を選び、冪倍の合成式から admissible 性と自由化を得る。
規約：KST §5、Stacks 0815、チャートの全体被覆は行列式中心の被覆定理で保証される。
使われ方：有限加群の平坦化の特殊形を一般チャートへ移す入力。
-/
theorem exists_finiteRank_determinantal_flattening (f : R) (hf : f ∈ nonZeroDivisors R)
    (μ : M →ₗ[R] M') [IsLocalizedModule.Away f μ]
    (e : M' ≃ₗ[R] (ι → Localization.Away f)) :
    ∃ g : M →ₗ[R] (ι → R), (determinantalCenter g).FG ∧
      PrimeSpectrum.basicOpen f ≤ affineCenterComplement (determinantalCenter g) ∧
      ∀ m : ι → M,
        let I := determinantalCenter g
        let a := determinantalCenterGenerator g m
        letI : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
        Module.Flat (BlowupChartRing I a)
          (modulePureTransform (chartBaseMap I a f) (BlowupChartRing I a ⊗[R] M)) := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  obtain ⟨n, g, h, hh, hg⟩ := exists_finiteRank_isogeny f μ e
  have hn := boundary_pow_mem_determinantalCenter g h f n hg
  exact ⟨g, IsNoetherian.noetherian _,
    basicOpen_le_affineCenterComplement_of_pow_mem (determinantalCenter g) f
      (n * Fintype.card ι) hn,
    fun m => determinantalChartPureTransform_flat g m h f n hh hf⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
