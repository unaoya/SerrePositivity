module

public import SerrePositivity.AlgebraicGeometry.GenericHigherMinorVanishing
public import SerrePositivity.AlgebraicGeometry.TensorAlgebraBaseChangeFlat
public import SerrePositivity.AlgebraicGeometry.NormalizedCoefficientIdeal
public import Mathlib.RingTheory.Localization.BaseChange

/-!
概要：KST §5、Stacks 0810 の境界外だけで平坦な加群の高次小行列式の消滅。
方針：境界外へ基底変更して一般階数の消滅判定を使い、正則な局所化の単射性で戻す。
規約：元の加群の基礎環上の平坦性は仮定しない。
使われ方：境界外の一定階数から実際の係数中心の自由性判定を準備する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

/--
概要：境界外で平坦かつ一定の一般階数を持つ有限加群の高次関係式小行列式は元の代数で零。
方針：二つの基底変更表示の実同型と境界外での消滅判定を、正則な局所化の単射性へ接続する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、実際の分裂表示を入力する。
使われ方：係数中心の全チャートで純変換が一般点で自由となるための高次消滅。
-/
theorem higherMinorIdeal_eq_bot_of_boundary_genericRank
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {M ι m n : Type*} [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M] [Fintype m] [Finite n]
    (e : B →ₗ[A] (ι →₀ A)) (p : (ι →₀ A) →ₗ[A] B) (hpe : p.comp e = LinearMap.id)
    (q : (m → B) →ₗ[B] M) (hq : Function.Surjective q) (H : Matrix m n B)
    (hH : Submodule.span B (Set.range H.col) = LinearMap.ker q)
    (f : A) (hf : IsRegular f)
    [Module.Flat (Localization.Away f) ((Localization.Away f) ⊗[A] M)] (r : ℕ)
    (hrank :
      let F := Localization.Away f
      let D := F ⊗[A] B
      letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
      letI : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap F D))) :=
        geometricallyIntegral_tensorProjection A B F
      ∀ P : PrimeSpectrum F,
        let L := Localization.AtPrime (geometricallyIntegralGenericPrime F D P).asIdeal
        Module.finrank L (L ⊗[D] (D ⊗[B] M)) = r)
    (j : ℕ) (hj : Fintype.card m - r < j) : matrixMinorIdeal H j = ⊥ := by
  classical
  let F := Localization.Away f
  let D := F ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap F D))) :=
    geometricallyIntegral_tensorProjection A B F
  let : Module.Flat F (D ⊗[B] M) := tensorAlgebraBaseChange_flat A B F M
  let e' := splitAlgebraTensorEmbedding (C := F) e
  let p' := splitAlgebraTensorRetraction (C := F) p
  have hs : p'.comp e' = LinearMap.id := splitAlgebraTensorRetraction_comp_embedding e p hpe
  let qD := finiteFreePresentationBaseChange (C := D) q
  have hqD : Function.Surjective qD := finiteFreePresentationBaseChange_surjective q hq
  have hker := finiteFreePresentationBaseChange_columnSpan_eq_ker (C := D) H q hq hH
  have hrankD : ∀ P : PrimeSpectrum F,
      let L := Localization.AtPrime (geometricallyIntegralGenericPrime F D P).asIdeal
      Module.finrank L (L ⊗[D] (D ⊗[B] M)) = r := hrank
  have hzeroD : matrixMinorIdeal (H.map (algebraMap B D)) j = ⊥ :=
    higherMinorIdeal_eq_bot_of_constant_genericRank F D e' p' hs qD hqD
      (H.map (algebraMap B D)) hker r hrankD j hj
  have hmap : (matrixMinorIdeal H j).map (algebraMap B D) = ⊥ := by
    rw [matrixMinorIdeal_map]
    exact hzeroD
  let : IsLocalization (Submonoid.powers (algebraMap A B f)) D := by
    rw [← Algebra.algebraMapSubmonoid_powers]
    infer_instance
  have hφ : Function.Injective (algebraMap B D) :=
    IsLocalization.injective D (Submonoid.powers_le.mpr
      (isRegular_iff_mem_nonZeroDivisors.mp
        (algebraMap_isRegular_of_split_coefficients e p hpe f hf)))
  apply bot_unique
  intro x hx
  apply (Ideal.mem_bot).mpr
  apply hφ
  have hmem := Ideal.mem_map_of_mem (algebraMap B D) hx
  rw [hmap] at hmem
  simpa only [map_zero] using (Ideal.mem_bot).mp hmem

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
