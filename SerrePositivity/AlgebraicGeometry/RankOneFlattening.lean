module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.RankOneIsogeny
public import SerrePositivity.AlgebraicGeometry.LinearMapTensorImage
public import SerrePositivity.AlgebraicGeometry.IdealFlattening

/-!
概要：KST §5、Stacks 0815 の平坦化を境界外で階数一自由な有限表示加群に構成する。
方針：局所化同型の分母を払い、環への写像の像イデアルを中心とする。
規約：一般の有限型代数上の有限加群の平坦化とは区別する。
使われ方：Noether 特殊形に向けた実際の平坦化中心の先行例。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R C M : Type*} [CommRing R] [CommRing C] [Algebra R C]
  [AddCommGroup M] [Module R M]

/--
概要：冪倍の左逆元を持つ環への写像は純変換を像イデアルに同定する。
方針：基底変更後の核の冪消滅と標的での正則作用を使う。
規約：KST §5、Stacks 0815、境界元の像は係数環上正則。
使われ方：階数一自由な場合の純変換のチャートでの自明化。
-/
def rankOnePureTransformEquivImage (g : M →ₗ[R] R) (h : R →ₗ[R] M)
    (f : R) (n : ℕ) (hh : h.comp g = f ^ n • LinearMap.id)
    (hf : IsRegular (algebraMap R C f)) :
    modulePureTransform (algebraMap R C f) (C ⊗[R] M) ≃ₗ[C]
      Ideal.map (algebraMap R C) (LinearMap.range g) :=
  (modulePureTransformEquivImage (algebraMap R C f) (linearMapTensorToAlgebra g)
    (Module.Flat.isSMulRegular_of_isRegular hf)
    (fun z hz => ⟨n, by
      rw [← map_pow]
      exact linearMapTensorToAlgebra_ker_annihilated g h (f ^ n) hh z hz⟩)).trans
      (LinearEquiv.ofEq _ _ (linearMapTensorToAlgebra_range g))

/--
概要：冪倍の右逆元があれば像イデアルは境界の冪を含む。
方針：環側の合成式を一に適用する。
規約：KST §5、Stacks 0815、境界の正則性は不要。
使われ方：選んだ中心の admissible 性。
-/
theorem boundary_pow_mem_range_of_isogeny (g : M →ₗ[R] R) (h : R →ₗ[R] M)
    (f : R) (n : ℕ) (hh : g.comp h = f ^ n • LinearMap.id) :
    f ^ n ∈ LinearMap.range g := by
  refine ⟨h 1, ?_⟩
  simpa using LinearMap.congr_fun hh 1

/--
概要：冪倍で環と同型な加群の純変換は像イデアルの blowup チャート上自由。
方針：純変換を拡大像イデアルに移し、例外イデアルの自由化を使う。
規約：KST §5、Stacks 0815、チャートの代数構造はその係数写像。
使われ方：階数一自由な場合の実際の平坦化。
-/
def chartRankOnePureTransformEquiv (g : M →ₗ[R] R) (h : R →ₗ[R] M)
    (f : R) (n : ℕ) (hh : h.comp g = f ^ n • LinearMap.id)
    (hf : f ∈ nonZeroDivisors R) (a : (LinearMap.range g : Ideal R)) :
    let I : Ideal R := LinearMap.range g
    letI : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
    modulePureTransform (chartBaseMap I a f) (BlowupChartRing I a ⊗[R] M) ≃ₗ[
      BlowupChartRing I a] BlowupChartRing I a := by
  let I : Ideal R := LinearMap.range g
  letI : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
  have hreg : IsRegular (algebraMap R (BlowupChartRing I a) f) :=
    isRegular_iff_mem_nonZeroDivisors.mpr (chartBaseMap_nonZeroDivisors I a hf)
  exact (rankOnePureTransformEquivImage g h f n hh hreg).trans
    (chartExceptionalIdealEquiv I a).symm

/--
概要：境界外で階数一自由な有限表示加群に実際の admissible な平坦化中心が存在。
方針：局所化同型の分母を払い、像イデアルの blowup 上で純変換を自由化する。
規約：KST §5、Stacks 0815、有限性は基礎環上での有限表示性。
使われ方：一般の有限型加群の場合とは区別した平坦化の特殊形。
-/
theorem exists_rankOne_flattening_center
    [Module.FinitePresentation R M] {M' : Type*} [AddCommGroup M'] [Module R M']
    (f : R) (hf : f ∈ nonZeroDivisors R) (μ : M →ₗ[R] M')
    [IsLocalizedModule.Away f μ] (e : M' ≃ₗ[R] Localization.Away f) :
    ∃ I : Ideal R, I.FG ∧ PrimeSpectrum.basicOpen f ≤ affineCenterComplement I ∧
      ∀ a : I, letI : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
        Module.Flat (BlowupChartRing I a)
          (modulePureTransform (chartBaseMap I a f) (BlowupChartRing I a ⊗[R] M)) := by
  obtain ⟨n, g, h, hh, hg⟩ := exists_rankOne_isogeny f μ e
  let I : Ideal R := LinearMap.range g
  have hn : f ^ n ∈ I := boundary_pow_mem_range_of_isogeny g h f n hg
  refine ⟨I, Submodule.fg_range g,
    basicOpen_le_affineCenterComplement_of_pow_mem I f n hn, ?_⟩
  intro a
  let : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
  exact Module.Flat.of_linearEquiv (chartRankOnePureTransformEquiv g h f n hh hf a)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
