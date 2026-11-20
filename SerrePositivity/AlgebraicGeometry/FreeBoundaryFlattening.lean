module

public import SerrePositivity.AlgebraicGeometry.FiniteModuleFreeLocusFlattening
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
概要：KST §5、Stacks 0815 の境界外の自由性だけを入力する有限加群の平坦化。
方針：自由な局所化加群の有限基底を選び、有限階数の場合の実際の中心を使う。
規約：零環と階数零を含めて基底添字の有限性で扱う。
使われ方：分子中心の各チャートに局所平坦化を適用する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R M N : Type*} [CommRing R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]
  [AddCommGroup N] [Module R N]

/--
概要：境界外で自由な有限加群に、全標準チャート上で純変換を平坦にする admissible 中心が存在。
方針：局所化先の有限生成性を基底変更から得て、選んだ有限基底で既証明の有限階数の場合へ移す。
規約：KST §5、Stacks 0815、自由加群の基底や階数を利用者に選ばせない。
使われ方：自由な基本開からの局所平坦化中心の選択。
-/
theorem exists_freeBoundary_flattening_center (f : R) (hf : f ∈ nonZeroDivisors R)
    [Module (Localization.Away f) N] [IsScalarTower R (Localization.Away f) N]
    (μ : M →ₗ[R] N) [IsLocalizedModule.Away f μ]
    [Module.Free (Localization.Away f) N] :
    ∃ I : Ideal R, I.FG ∧ PrimeSpectrum.basicOpen f ≤ affineCenterComplement I ∧
      ∀ a : I, letI : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
        Module.Flat (BlowupChartRing I a)
          (modulePureTransform (chartBaseMap I a f) (BlowupChartRing I a ⊗[R] M)) := by
  classical
  let L := Localization.Away f
  let eμ := (IsLocalizedModule.isBaseChange (Submonoid.powers f) L μ).equiv
  have : Module.Finite L N := Module.Finite.of_surjective eμ.toLinearMap eμ.surjective
  let e := (Module.Free.chooseBasis L N).repr.trans
    (Finsupp.linearEquivFunOnFinite L L (Module.Free.ChooseBasisIndex L N))
  exact exists_finiteRank_flattening_center f hf μ (e.restrictScalars R)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
