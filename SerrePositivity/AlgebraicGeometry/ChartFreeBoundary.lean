module

public import SerrePositivity.AlgebraicGeometry.ChartBoundaryLocalization
public import SerrePositivity.AlgebraicGeometry.FreeTensorBaseChange
public import Mathlib.RingTheory.Localization.BaseChange

/-!
概要：KST §5、Stacks 0815 の分子チャートの境界外での加群の自由性。
方針：自由な基本開への実際の係数写像を使い、二段の基底変更で自由性を移す。
規約：元の環・境界外の環・自由化基本開の環を区別する。
使われ方：境界外で平坦な有限加群を有限階数自由な場合の平坦化に還元する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/--
概要：自由化係数の分子のチャートでは、元の加群の基底変更は境界外で自由。
方針：自由化基本開からチャートの境界外への環準同型を使い、局所化の基底変更同型を合成する。
規約：KST §5、Stacks 0815、局所化先 N とその実際の局所化写像を入力する。
使われ方：各分子チャート上で有限階数自由の場合の平坦化を適用する。
-/
theorem chart_free_away_boundary_of_free_localization
    (I : Ideal R) (a : I) (f : R) (n : ℕ) (hn : f ^ n ∈ I)
    [Module (Localization.Away f) N] [IsScalarTower R (Localization.Away f) N]
    (μ : M →ₗ[R] N) [IsLocalizedModule.Away f μ]
    (x : Localization.Away f)
    [Module.Free (Localization.Away x) (LocalizedModule.Away x N)]
    (hx : (IsLocalization.Away.sec f x).1 = a.val) :
    letI : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
    Module.Free (Localization.Away (chartBaseMap I a f))
      (LocalizedModule.Away (chartBaseMap I a f) (BlowupChartRing I a ⊗[R] M)) := by
  let L := Localization.Away f
  let C := BlowupChartRing I a
  let K := Localization.Away (chartBaseMap I a f)
  let B := Localization.Away x
  let : Algebra R C := (chartBaseMap I a).toAlgebra
  let : Algebra R K := ((algebraMap C K).comp (chartBaseMap I a)).toAlgebra
  let : Algebra L K := (chartBoundaryBaseLift I a f).toAlgebra
  let : Algebra B K := (chartBoundaryFreeOpenLift I a f n hn x hx).toAlgebra
  let : Module R C := Algebra.toModule
  let : Module R K := Algebra.toModule
  let : SMul R C := (inferInstance : Algebra R C).toSMul
  let : SMul R K := (inferInstance : Algebra R K).toSMul
  let : SMul L K := (inferInstance : Algebra L K).toSMul
  have : IsScalarTower R C K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower R L K := IsScalarTower.of_algebraMap_eq
    (fun r => (chartBoundaryBaseLift_base I a f r).symm)
  have : IsScalarTower L B K := IsScalarTower.of_algebraMap_eq
    (fun y => (chartBoundaryFreeOpenLift_base I a f n hn x hx y).symm)
  let ν := LocalizedModule.mkLinearMap (Submonoid.powers x) N
  have hν : IsBaseChange B ν :=
    IsLocalizedModule.isBaseChange (Submonoid.powers x) B ν
  have : Module.Free K (K ⊗[L] N) := free_tensor_of_free_baseChange ν hν
  have hμ : IsBaseChange L μ := IsLocalizedModule.isBaseChange (Submonoid.powers f) L μ
  have : Module.Free K (K ⊗[R] M) := free_tensor_of_free_baseChange μ hμ
  let η := LocalizedModule.mkLinearMap (Submonoid.powers (chartBaseMap I a f)) (C ⊗[R] M)
  let eLoc := (IsLocalizedModule.isBaseChange
    (Submonoid.powers (chartBaseMap I a f)) K η).equiv
  let eCancel := TensorProduct.AlgebraTensorModule.cancelBaseChange R C K K M
  exact Module.Free.of_equiv (eCancel.symm.trans eLoc)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
