module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.GenericBoundaryPureFree
public import SerrePositivity.AlgebraicGeometry.BoundaryMultipleCenter
public import SerrePositivity.AlgebraicGeometry.GeometricallyIntegralExtendedPrime
public import SerrePositivity.AlgebraicGeometry.BlowupChartIdeals
public import SerrePositivity.AlgebraicGeometry.ChartBoundaryRegular

/-!
概要：KST §5、Stacks 0810 の実際の係数 blowup のチャート上の一般点での純変換の自由性。
方針：チャートで正則な係数生成元を選び、幾何学的整性による拡大素性へ自由性判定を適用する。
規約：係数中心・チャート・拡大素点の局所環は実際に構成したものを使う。
使われ方：純変換の自由 locus が基礎環を覆うための一般点での入力。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：実際の係数 blowup の全標準チャートで、拡大素点における境界純変換は自由。
方針：共通因子と可除性をチャートから選び、境界の正則性と拡大素性を証明して自由性判定を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、境界冪の指数と表示の生成元数を区別する。
使われ方：係数中心の純変換の自由 locus が各基礎素点に当たることを示す準備。
-/
theorem coefficientBlowup_chart_boundary_free_and_finrank
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {M ι m n : Type*} [AddCommGroup M] [Module B M] [Fintype m] [Finite n]
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (H : Matrix m n B) (k : ℕ) (q : (m → B) →ₗ[B] M) (hq : Function.Surjective q)
    (hH : Submodule.span B (Set.range H.col) = LinearMap.ker q)
    (hzero : matrixMinorIdeal H (k + 1) = ⊥) (f : A) (hf : IsRegular f)
    (N : ℕ) (hn : f ^ N ∈ splitAlgebraCoefficientIdeal e (matrixMinorIdeal H k))
    (a : boundaryMultipleCenter f (splitAlgebraCoefficientIdeal e (matrixMinorIdeal H k))) :
    let J := boundaryMultipleCenter f (splitAlgebraCoefficientIdeal e (matrixMinorIdeal H k))
    let C := BlowupChartRing J a
    letI : Algebra A C := (chartBaseMap J a).toAlgebra
    letI : IsNoetherianRing C := blowupChartRing_isNoetherianRing J a
    GenericBoundaryPureFree A B C M (chartBaseMap J a f) (Fintype.card m - k) := by
  classical
  let J := boundaryMultipleCenter f (splitAlgebraCoefficientIdeal e (matrixMinorIdeal H k))
  let C := BlowupChartRing J a
  let : Algebra A C := (chartBaseMap J a).toAlgebra
  let : IsNoetherianRing C := blowupChartRing_isNoetherianRing J a
  obtain ⟨c, hc, hcoeff, hcf⟩ := boundaryMultipleCenter_chart_regular_principal_dvd_pow f
    (splitAlgebraCoefficientIdeal e (matrixMinorIdeal H k)) N hn a
  have hfC : IsRegular (chartBaseMap J a f) :=
    isRegular_iff_mem_nonZeroDivisors.mpr
      (chartBaseMap_nonZeroDivisors J a (isRegular_iff_mem_nonZeroDivisors.mp hf))
  exact genericBoundaryPureFree_of_coefficient_minor (A := A) (B := B) (C := C) (M := M)
    e p hpe H k q hq hH hzero c
    (chartBaseMap J a f) (isRegular_iff_mem_nonZeroDivisors.mpr hc) hfC N hcf hcoeff

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
