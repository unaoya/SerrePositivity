module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.GenericPrimeBaseChange
public import Mathlib.RingTheory.IsTensorProduct

/-!
概要：KST §5、Stacks 0810・0811 の代数の押し出しの任意の実現での拡大一般点の縮約。
方針：標準テンソル積との実際の代数同型で拡大イデアルを比較する。
規約：構造写像と両側の実際の一般点を保持する。
使われ方：二段テンソル積を別の基底変更表示へ移して一般点の局所比較を適用する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/--
概要：代数の押し出しの任意の実現において、拡大一般点の元の代数への縮約は縮約基礎素点の拡大一般点。
方針：押し出し同型が構造写像と拡大イデアルを保つことから、標準テンソル積の場合へ戻す。
規約：KST §5、Stacks 0810・0811、両代数の幾何学的整性と実分裂を明示する。
使われ方：基底変更した純変換の一般点自由性をテンソル積の表示に依存せず比較する。
-/
theorem geometricallyIntegralGenericPrime_pushout_comap
    (A B C D : Type u) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B D] [Algebra C D]
    [IsScalarTower A B D] [IsScalarTower A C D] [Algebra.IsPushout A C B D]
    [IsNoetherianRing A] [IsNoetherianRing C]
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    [Module.Flat C D] [Algebra.FinitePresentation C D]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C D)))]
    {ι : Type*} (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B)
    (hpe : p.comp e = LinearMap.id) (P : PrimeSpectrum C) :
    PrimeSpectrum.comap (algebraMap B D) (geometricallyIntegralGenericPrime C D P) =
      geometricallyIntegralGenericPrime A B (PrimeSpectrum.comap (algebraMap A C) P) := by
  let T := C ⊗[A] B
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C T))) :=
    geometricallyIntegral_tensorProjection A B C
  let E : T ≃ₐ[C] D := Algebra.IsPushout.equiv A C B D
  let φ : B →+* T := (Algebra.TensorProduct.includeRight : B →ₐ[A] T).toRingHom
  have hB : E.toRingHom.comp φ = algebraMap B D := by
    ext b
    change (Algebra.IsPushout.equiv A C B D) ((1 : C) ⊗ₜ[A] b) = algebraMap B D b
    simp only [Algebra.IsPushout.equiv_tmul, map_one, one_mul]
  have hC : E.toRingHom.comp (algebraMap C T) = algebraMap C D := by
    ext c
    exact E.commutes c
  have hprime : PrimeSpectrum.comap E.toRingHom (geometricallyIntegralGenericPrime C D P) =
      geometricallyIntegralGenericPrime C T P := by
    apply PrimeSpectrum.ext
    change (P.asIdeal.map (algebraMap C D)).comap E.toRingHom =
      P.asIdeal.map (algebraMap C T)
    rw [← hC, ← Ideal.map_map, Ideal.comap_map_of_bijective E.toRingHom E.bijective]
  calc
    PrimeSpectrum.comap (algebraMap B D) (geometricallyIntegralGenericPrime C D P) =
        PrimeSpectrum.comap φ
          (PrimeSpectrum.comap E.toRingHom (geometricallyIntegralGenericPrime C D P)) := by
      rw [← PrimeSpectrum.comap_comp_apply, hB]
    _ = geometricallyIntegralGenericPrime A B (PrimeSpectrum.comap (algebraMap A C) P) := by
      rw [hprime]
      exact geometricallyIntegralGenericPrime_baseChange_comap A B C e p hpe P

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
