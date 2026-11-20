module

public import SerrePositivity.AlgebraicGeometry.BoundaryMultipleCenter
public import SerrePositivity.AlgebraicGeometry.SplitAlgebraCoefficientBaseChange
public import SerrePositivity.AlgebraicGeometry.SplitAlgebraCoefficientMembership

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の係数中心の実 blowup と代数イデアルの可除性。
方針：境界元倍の係数中心と係数イデアルの基底変更公式を接続する。
規約：代数の分裂表示は明示的なデータとして入力し、一般形の平坦化はここでは主張しない。
使われ方：小行列式イデアルの全元を共通の正則元で割るチャートの構成。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R B ι : Type*} [CommRing R] [CommRing B] [Algebra R B]

/--
概要：境界外の素点で消えない有限生成代数イデアルから、有限生成な境界元倍の係数中心を得る。
方針：係数イデアルの有限生成性と境界冪の所属を使い、中心の補開集合を D(f) と同定する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、代数の分裂表示は明示的に入力する。
使われ方：実際の admissible な係数 blowup 中心の構成。
-/
theorem coefficientBlowupCenter_fg_complement
    (e : B →ₗ[R] (ι →₀ R)) (p : (ι →₀ R) →ₗ[R] B)
    (hpe : p.comp e = LinearMap.id) (f : R) (J : Ideal B) (hJfg : J.FG)
    (hJ : ∀ q : Ideal R, q.IsPrime → f ∉ q → ¬ J ≤ q.map (algebraMap R B)) :
    (boundaryMultipleCenter f (splitAlgebraCoefficientIdeal e J)).FG ∧
      affineCenterComplement (boundaryMultipleCenter f (splitAlgebraCoefficientIdeal e J)) =
        PrimeSpectrum.basicOpen f := by
  obtain ⟨n, hn⟩ := exists_pow_mem_splitAlgebraCoefficientIdeal e p hpe J f hJ
  exact ⟨boundaryMultipleCenter_fg f _ (splitAlgebraCoefficientIdeal_fg e p hpe J hJfg),
    boundaryMultipleCenter_complement f _ n hn⟩

/--
概要：境界元倍の係数中心の実チャートで、代数イデアルの拡大は係数環の一つの正則元で割り切れる。
方針：係数イデアルを正則単項化し、その基底変更と拡大イデアルへの所属判定を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、境界元の元の環での正則性は不要。
使われ方：有限型平坦化でチャート上の小行列式の共通因子を得る。
-/
theorem coefficientBlowupCenter_chart_divisibility
    (e : B →ₗ[R] (ι →₀ R)) (p : (ι →₀ R) →ₗ[R] B)
    (hpe : p.comp e = LinearMap.id) (f : R) (J : Ideal B)
    (a : boundaryMultipleCenter f (splitAlgebraCoefficientIdeal e J)) :
    let C := BlowupChartRing (boundaryMultipleCenter f (splitAlgebraCoefficientIdeal e J)) a
    letI : Algebra R C :=
      (chartBaseMap (boundaryMultipleCenter f (splitAlgebraCoefficientIdeal e J)) a).toAlgebra
    ∃ c : C, c ∈ nonZeroDivisors C ∧
      J.map (Algebra.TensorProduct.includeRight : B →ₐ[R] C ⊗[R] B).toRingHom ≤
        Ideal.span {algebraMap C (C ⊗[R] B) c} := by
  classical
  let C := BlowupChartRing (boundaryMultipleCenter f (splitAlgebraCoefficientIdeal e J)) a
  let : Algebra R C :=
    (chartBaseMap (boundaryMultipleCenter f (splitAlgebraCoefficientIdeal e J)) a).toAlgebra
  obtain ⟨c, hc, hC, _⟩ := boundaryMultipleCenter_chart_regular_principal f
    (splitAlgebraCoefficientIdeal e J) a
  let e' := splitAlgebraTensorEmbedding (C := C) e
  let p' := splitAlgebraTensorRetraction (C := C) p
  let φ : B →+* C ⊗[R] B :=
    (Algebra.TensorProduct.includeRight : B →ₐ[R] C ⊗[R] B).toRingHom
  have hs : p'.comp e' = LinearMap.id := splitAlgebraTensorRetraction_comp_embedding e p hpe
  have hcoeff : splitAlgebraCoefficientIdeal e' (J.map φ) = Ideal.span {c} :=
    (splitAlgebraCoefficientIdeal_baseChange e p hpe J).trans hC
  refine ⟨c, hc, ?_⟩
  have h := (splitAlgebraCoefficientIdeal_le_iff e' p' hs (J.map φ) (Ideal.span {c})).mp hcoeff.le
  simpa only [Ideal.map_span, Set.image_singleton] using h

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
