module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.FreeBoundaryFlattening
public import SerrePositivity.AlgebraicGeometry.BlowupChartIdeals
public import SerrePositivity.AlgebraicGeometry.ChartBoundaryRegular

/-!
概要：KST §5、Stacks 0815 の境界外が自由なチャート上での局所平坦化中心。
方針：チャート環の Noether 性と基底変更加群の有限性から自由境界の場合を適用する。
規約：出力の中心は最初の blowup のチャート環のイデアル。
使われ方：局所中心の延長と共通細分による大域平坦化。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
  (I : Ideal R) (a : I) (f : R) (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]

set_option backward.isDefEq.respectTransparency false in
/--
概要：境界外が自由な標準チャートには純変換を平坦にする実際の局所中心が存在。
方針：チャート上の有限加群に自由境界の平坦化を適用する。
規約：KST §5、Stacks 0815、二段目の中心とチャートのテンソル積を明示する。
使われ方：分子中心の生成元チャートごとの局所中心の選択。
-/
theorem exists_chart_flattening_center (hf : f ∈ nonZeroDivisors R)
    (hfree : letI : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
      Module.Free (Localization.Away (chartBaseMap I a f))
        (LocalizedModule.Away (chartBaseMap I a f) (BlowupChartRing I a ⊗[R] M))) :
    let A := BlowupChartRing I a
    letI : Algebra R A := (chartBaseMap I a).toAlgebra
    ∃ K : Ideal A, K.FG ∧ PrimeSpectrum.basicOpen (chartBaseMap I a f) ≤ affineCenterComplement K ∧
      ∀ b : K, letI : Algebra A (BlowupChartRing K b) := (chartBaseMap K b).toAlgebra
        Module.Flat (BlowupChartRing K b)
          (modulePureTransform (chartBaseMap K b (chartBaseMap I a f))
            (BlowupChartRing K b ⊗[A] (A ⊗[R] M))) := by
  let A := BlowupChartRing I a
  let : Algebra R A := (chartBaseMap I a).toAlgebra
  have : Module.Free (Localization.Away (chartBaseMap I a f))
      (LocalizedModule.Away (chartBaseMap I a f) (A ⊗[R] M)) := hfree
  with_reducible_and_instances
    exact exists_freeBoundary_flattening_center
      (N := LocalizedModule.Away (chartBaseMap I a f) (A ⊗[R] M)) (chartBaseMap I a f)
      (chartBaseMap_nonZeroDivisors I a hf)
      (LocalizedModule.mkLinearMap (Submonoid.powers (chartBaseMap I a f)) (A ⊗[R] M))

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
