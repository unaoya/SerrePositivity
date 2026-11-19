module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.GeometricallyIntegralGenericFreeness
public import SerrePositivity.AlgebraicGeometry.SplitAlgebraTensorCoefficients
public import SerrePositivity.AlgebraicGeometry.SplitAlgebraCoefficientMembership

/-!
概要：KST §5、Stacks 0810・0811 の拡大一般点と任意の基底変更の両立性。
方針：拡大イデアルへの所属を分裂表示の係数で照合する。
規約：基底変更環の平坦性は仮定せず、代数の実分裂を明示する。
使われ方：境界外の開閉階数部分を分離した後、実チャート上の一般階数を照合する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [IsNoetherianRing A] [IsNoetherianRing C]
  [Module.Flat A B] [Algebra.FinitePresentation A B]
  [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]

/--
概要：任意の基底変更後の拡大素点の元の代数への縮約は、縮約した基礎素点の拡大素点。
方針：分裂の基底変更後の係数と元の係数の像を比較してイデアルの所属を照合する。
規約：KST §5、Stacks 0810・0811、係数環の平坦性は不要。
使われ方：blowup チャートへの基底変更後の一般階数の保存。
-/
theorem geometricallyIntegralGenericPrime_baseChange_comap {ι : Type*}
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B)
    (hpe : p.comp e = LinearMap.id) (P : PrimeSpectrum C) :
    let D := C ⊗[A] B
    letI : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
      geometricallyIntegral_tensorProjection A B C
    PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] D).toRingHom
        (geometricallyIntegralGenericPrime C D P) =
      geometricallyIntegralGenericPrime A B (PrimeSpectrum.comap (algebraMap A C) P) := by
  let D := C ⊗[A] B
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
    geometricallyIntegral_tensorProjection A B C
  let e' := splitAlgebraTensorEmbedding (C := C) e
  let p' := splitAlgebraTensorRetraction (C := C) p
  have hs : p'.comp e' = LinearMap.id := splitAlgebraTensorRetraction_comp_embedding e p hpe
  apply PrimeSpectrum.ext
  ext b
  change ((1 : C) ⊗ₜ[A] b) ∈ P.asIdeal.map (algebraMap C D) ↔
    b ∈ (P.asIdeal.comap (algebraMap A C)).map (algebraMap A B)
  rw [splitAlgebra_mem_map_iff e' p' hs, splitAlgebra_mem_map_iff e p hpe]
  simp only [e', splitAlgebraTensorEmbedding_tmul, mul_one, Ideal.mem_comap]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
