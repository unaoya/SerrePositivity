module

public import SerrePositivity.AlgebraicGeometry.BoundaryGenericRankCharts
public import SerrePositivity.AlgebraicGeometry.FreeLocusLocalizationBaseChange
public import SerrePositivity.AlgebraicGeometry.GenericPrimeBaseChange

/-!
概要：KST §5、Stacks 0810・0811 の境界外一般階数と元の代数の局所階数。
方針：境界外の相対平坦性による自由性を一元局所化から戻し、縮約素点で局所階数を照合する。
規約：加群の平坦性は境界外だけで仮定する。
使われ方：階数部分を分離した実チャートの一般階数を元の階数関数と比較する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing A] [Module.Flat A B] [Algebra.FinitePresentation A B]
  [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
  (M : Type*) [AddCommGroup M] [Module A M] [Module B M]
  [IsScalarTower A B M] [Module.Finite B M]
  {ι : Type*} (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B)
  (hpe : p.comp e = LinearMap.id) (f : A)
  [Module.Flat (Localization.Away f) ((Localization.Away f) ⊗[A] M)]

include e p hpe

/--
概要：境界外で相対平坦な有限加群は、境界外の基礎素点に対応する元の代数の一般点で自由。
方針：境界局所化後の一般点で自由性を得て、一元局所化の自由 locus の等式と縮約素点の比較を使う。
規約：KST §5、Stacks 0810・0811、元の加群が全体で相対平坦であるとは仮定しない。
使われ方：任意のチャートへの基底変更で局所階数を運ぶための自由性。
-/
theorem genericPrime_mem_freeLocus_of_boundary_flat (P : PrimeSpectrum (Localization.Away f)) :
    geometricallyIntegralGenericPrime A B
      (PrimeSpectrum.comap (algebraMap A (Localization.Away f)) P) ∈ Module.freeLocus B M := by
  let F := Localization.Away f
  let D := F ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap F D))) :=
    geometricallyIntegral_tensorProjection A B F
  let : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing F D
  let : Module.FinitePresentation D (D ⊗[B] M) := Module.finitePresentation_of_finite D _
  let : Module.Flat F (D ⊗[B] M) := tensorAlgebraBaseChange_flat A B F M
  let Q := geometricallyIntegralGenericPrime F D P
  have hfree : Q ∈ Module.freeLocus D (D ⊗[B] M) := by
    exact (Module.mem_freeLocus_iff_tensor (M := D ⊗[B] M) Q
      (Localization.AtPrime Q.asIdeal)).mpr (free_at_geometricallyIntegralGenericPrime F D P)
  have hQ : PrimeSpectrum.comap (algebraMap B D) Q =
      geometricallyIntegralGenericPrime A B (PrimeSpectrum.comap (algebraMap A F) P) :=
    geometricallyIntegralGenericPrime_baseChange_comap A B F e p hpe P
  have h := (mem_freeLocus_baseChange_iff_of_isLocalization
    (Algebra.algebraMapSubmonoid B (Submonoid.powers f)) Q).mp hfree
  rwa [hQ] at h

/--
概要：境界外一般階数は、元の代数の対応する一般点での局所階数と一致する。
方針：境界局所化の縮約素点を照合し、その素点で自由な加群の局所階数の基底変更保存を使う。
規約：KST §5、Stacks 0810・0811、境界外の相対平坦性だけを要求する。
使われ方：境界外階数関数の引き戻しをチャート上の実際の加群の階数と同定する。
-/
theorem boundaryGenericRank_eq_original_rankAtStalk (P : PrimeSpectrum (Localization.Away f)) :
    boundaryGenericRank A B M f P = Module.rankAtStalk M
      (geometricallyIntegralGenericPrime A B
        (PrimeSpectrum.comap (algebraMap A (Localization.Away f)) P)) := by
  let F := Localization.Away f
  let D := F ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap F D))) :=
    geometricallyIntegral_tensorProjection A B F
  let Q := geometricallyIntegralGenericPrime F D P
  have hQ : PrimeSpectrum.comap (algebraMap B D) Q =
      geometricallyIntegralGenericPrime A B (PrimeSpectrum.comap (algebraMap A F) P) :=
    geometricallyIntegralGenericPrime_baseChange_comap A B F e p hpe P
  have hfree : Q.comap (algebraMap B D) ∈ Module.freeLocus B M := by
    rw [hQ]
    exact genericPrime_mem_freeLocus_of_boundary_flat A B M e p hpe f P
  change Module.finrank (Localization.AtPrime Q.asIdeal)
    (Localization.AtPrime Q.asIdeal ⊗[D] (D ⊗[B] M)) = _
  rw [← Module.rankAtStalk_eq_finrank_tensorProduct,
    rankAtStalk_baseChange_of_mem_freeLocus Q hfree, hQ]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
