module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.PureTransformOpenLocality
public import SerrePositivity.AlgebraicGeometry.PureTransformFlatSpec
public import SerrePositivity.AlgebraicGeometry.ChartGluing
public import SerrePositivity.AlgebraicGeometry.BlowupChartIdeals
public import SerrePositivity.AlgebraicGeometry.ChartBoundaryRegular

/-!
概要：KST §5、Stacks 0815 の通常 blowup のチャート上の純変換の平坦性を大域的な引き戻しの性質へ接続する。
方針：標準アフィンチャートの Noether 性と係数写像の公式を使い、開被覆で貼り合わせる。
規約：元の加群は Noether 基礎環上有限。
使われ方：平坦化した blowup を支配する共通細分へ平坦性を移す。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

/--
概要：通常 blowup の全チャートで純変換が平坦なら正則な境界を持つ全アフィン引き戻しでも平坦。
方針：各チャートを Noether アフィンモデルとして扱い、標準開被覆の局所性を使う。
規約：KST §5、Stacks 0815、実際の blowup 構造射について主張する。
使われ方：支配射への前合成によって平坦化を保存する。
-/
theorem hasFlatPurePullbacks_affineBlowup {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (f : R) (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hflat : ∀ a : I, letI : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
      Module.Flat (BlowupChartRing I a)
        (modulePureTransform (chartBaseMap I a f) (BlowupChartRing I a ⊗[R] M))) :
    HasFlatPurePullbacks (affineBlowupπ I) f M := by
  apply hasFlatPurePullbacks_of_openCover (affineBlowupπ I) f M
    (affineBlowupChartCover I).openCover
  intro a
  change HasFlatPurePullbacks (affineBlowupChartι I a ≫ affineBlowupπ I) f M
  rw [show affineBlowupChartι I a ≫ affineBlowupπ I =
    Spec.map (CommRingCat.ofHom (chartBaseMap I a)) from affineBlowupChartIso_inv_ι_π I a]
  have : IsNoetherianRing (CommRingCat.of (BlowupChartRing I a)) := by
    change IsNoetherianRing (BlowupChartRing I a)
    exact blowupChartRing_isNoetherianRing I a
  exact hasFlatPurePullbacks_spec (CommRingCat.ofHom (chartBaseMap I a)) f M (hflat a)

/--
概要：通常 blowup の全アフィン引き戻しの純変換が平坦なら全標準チャート上で平坦。
方針：標準チャートを試験対象とし、係数写像と境界の正則性を照合する。
規約：KST §5、Stacks 0815、元の境界元は基礎環で非零因子とする。
使われ方：一つの基礎環中心へ降ろした後の実際のチャート平坦性。
-/
theorem HasFlatPurePullbacks.affineBlowup_charts {R : Type u} [CommRing R]
    {I : Ideal R} {f : R} {M : Type v} [AddCommGroup M] [Module R M]
    (hp : HasFlatPurePullbacks (affineBlowupπ I) f M) (hf : f ∈ nonZeroDivisors R)
    (a : I) :
    letI : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
    Module.Flat (BlowupChartRing I a)
      (modulePureTransform (chartBaseMap I a f) (BlowupChartRing I a ⊗[R] M)) := by
  let A : CommRingCat.{u} := .of (BlowupChartRing I a)
  have he : pureTransformCoefficientMap (affineBlowupπ I) (affineBlowupChartι I a) =
      chartBaseMap I a := by
    unfold pureTransformCoefficientMap
    rw [show affineBlowupChartι I a ≫ affineBlowupπ I =
      Spec.map (CommRingCat.ofHom (chartBaseMap I a)) from affineBlowupChartIso_inv_ι_π I a,
      Spec.preimage_map]
    rfl
  let P (φ : R →+* A) : Prop :=
    letI : Algebra R A := φ.toAlgebra
    letI : Module R A := Algebra.toModule
    letI : SMul R A := (inferInstance : Algebra R A).toSMul
    IsRegular (φ f) → Module.Flat A (modulePureTransform (φ f) (A ⊗[R] M))
  have hchart : P (chartBaseMap I a) :=
    (congrArg P he).mp (hp A (affineBlowupChartι I a))
  exact hchart (isRegular_iff_mem_nonZeroDivisors.mpr (chartBaseMap_nonZeroDivisors I a hf))

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
