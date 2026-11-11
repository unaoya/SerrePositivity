module

public import SerrePositivity.AlgebraicGeometry.SmoothGenericHypersurface
import SerrePositivity.AlgebraicGeometry.AffineCommonPrincipalOpen
import SerrePositivity.AlgebraicGeometry.GenericTensorFractionEmbedding
import SerrePositivity.AlgebraicGeometry.GeometricFiberCommonOpen
import SerrePositivity.AlgebraicGeometry.HypersurfaceGeometricFiber
import SerrePositivity.AlgebraicGeometry.MvPolynomialGenericCoefficientDescent
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Smooth.Flat

/-!
概要：滑らかなアフィン射の生成ファイバーが幾何学的に整なら、ある稠密主開上の各ファイバーも幾何学的に整。
方針：モニック超曲面模型を主開へ降ろし、共通分数体から得た主開同型で各ファイバーを比較する。
規約：基底は整域とし、幾何学的整性は体へのテンソル積で表す。
使われ方：切断を通る滑らかなファイバー成分の構成可能性。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open MvPolynomial
open scoped TensorProduct nonZeroDivisors

/--
概要：整域上の滑らかな代数の生成ファイバーが幾何学的に整なら、
ある非零元を反転する任意の体への底変換が整域になる。
方針：生成ファイバーと双有理な絶対既約な超曲面を基底へ降ろし、共通の主開を通じて整性を移す。
規約：生成ファイバーの幾何学的整性は分数体の代数閉包へのテンソル積で仮定する。
使われ方：Stacks 055N の滑らかな場合における生成ファイバーの連結性の広がり。
-/
theorem exists_nonzero_forall_isDomain_tensor_of_smooth_generic
    {A B : Type u} {K : Type v} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Algebra.Smooth A B] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDomain (AlgebraicClosure K ⊗[K] (K ⊗[A] B))] :
    ∃ r : A, r ≠ 0 ∧ ∀ (F : Type w) [Field F] [Algebra A F], algebraMap A F r ≠ 0 →
      IsDomain (F ⊗[A] B) := by
  let B₀ := K ⊗[A] B
  let : Module.Free K B₀ := Module.Free.of_divisionRing K B₀
  let : IsDomain B₀ := Function.Injective.isDomain
    (Algebra.TensorProduct.includeRight : B₀ →ₐ[K] AlgebraicClosure K ⊗[K] B₀)
    (Algebra.TensorProduct.includeRight_injective
      (RingHom.injective (algebraMap K (AlgebraicClosure K))))
  let L := FractionRing B₀
  obtain ⟨n, p, hpMonic, hpIrred, j, hj, hFrac⟩ :=
    exists_absoluteIrreducible_monic_hypersurface_of_smooth (k := K) (B := B₀)
  obtain ⟨a, ha, q, hqMonic, hq⟩ := exists_away_monic_option_mvPolynomial_map_eq (A := A) p hpMonic
  let S := Localization.Away a
  have ha₀ : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp ha
  let : IsDomain S := Localization.Away.isDomain ha₀
  let sK : S →+* K := IsLocalization.Away.lift a (IsLocalization.map_units K (⟨a, ha⟩ : A⁰))
  let : Algebra S K := sK.toAlgebra
  let : IsScalarTower A S K := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.Away.lift_eq a _ x).symm
  let : IsFractionRing S K := IsFractionRing.isFractionRing_of_isLocalization
    (Submonoid.powers a) S K (powers_le_nonZeroDivisors_of_noZeroDivisors ha₀)
  let : IsScalarTower S K B₀ := TensorProduct.isScalarTower_left
  let : IsScalarTower S K L := OreLocalization.instIsScalarTower
  let B' := S ⊗[A] B
  let H := MvPolynomial (Option (Fin n)) S ⧸ Ideal.span {q}
  let H₀ := MvPolynomial (Option (Fin n)) K ⧸ Ideal.span {p}
  let : Module.Flat S H := flat_mvPolynomial_quotient_of_monic_option q hqMonic
  let eB := Algebra.TensorProduct.cancelBaseChange A S K K B
  have hI : (Ideal.span {q}).map (map (algebraMap S K)) = Ideal.span {p} := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {map sK q} = Ideal.span {p}
    rw [hq]
  let eH : K ⊗[S] H ≃ₐ[K] H₀ :=
    (mvPolynomialQuotientTensorEquiv (C := K) (Ideal.span {q})).trans
      (Ideal.quotientEquivAlgOfEq K hI)
  let iB := (IsScalarTower.toAlgHom K B₀ L).comp eB.toAlgHom
  let iH := j.comp eH.toAlgHom
  have hiB : Function.Injective iB := (IsFractionRing.injective B₀ L).comp eB.injective
  have hiH : Function.Injective iH := hj.comp eH.injective
  have hFracB (z : L) : ∃ x y, z = iB x / iB y := by
    obtain ⟨x, y, _, h⟩ := IsFractionRing.div_surjective B₀ z
    refine ⟨eB.symm x, eB.symm y, ?_⟩
    simpa [iB] using h.symm
  have hFracH (z : L) : ∃ x y, z = iH x / iH y := by
    obtain ⟨x, y, h⟩ := hFrac z
    refine ⟨eH.symm x, eH.symm y, ?_⟩
    simpa [iH] using h
  obtain ⟨f, hf, hFracf⟩ := exists_fraction_embedding_of_genericTensor iB hiB hFracB
  obtain ⟨g, hg, hFracg⟩ := exists_fraction_embedding_of_genericTensor iH hiH hFracH
  let : IsDomain B' := Function.Injective.isDomain f.toRingHom hf
  let : IsDomain H := Function.Injective.isDomain g.toRingHom hg
  let : Algebra B' L := f.toRingHom.toAlgebra
  let : Algebra H L := g.toRingHom.toAlgebra
  let : IsScalarTower S B' L := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  let : IsScalarTower S H L := IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  let : FaithfulSMul B' L := (faithfulSMul_iff_algebraMap_injective B' L).mpr hf
  let : FaithfulSMul H L := (faithfulSMul_iff_algebraMap_injective H L).mpr hg
  let : IsFractionRing B' L := by
    apply IsFractionRing.of_field
    exact hFracf
  let : IsFractionRing H L := by
    apply IsFractionRing.of_field
    exact hFracg
  obtain ⟨b, hb, c, hc, ⟨e⟩⟩ := exists_away_algEquiv_of_common_fractionField
    (A := S) (B := B') (C := H) (K := L)
  have hqIrred : Irreducible (map (algebraMap S (AlgebraicClosure K)) q) := by
    rw [IsScalarTower.algebraMap_eq S K (AlgebraicClosure K), ← map_map]
    change Irreducible (map (algebraMap K (AlgebraicClosure K)) (map sK q))
    rwa [hq]
  obtain ⟨t, ht, hModel⟩ := exists_nonzero_forall_isDomain_tensor_hypersurface q hqIrred
  obtain ⟨s, hs, hOpen⟩ := exists_nonzero_forall_isDomain_tensor_of_common_away
    t ht hModel (mem_nonZeroDivisors_iff_ne_zero.mpr hb)
    (mem_nonZeroDivisors_iff_ne_zero.mpr hc) e
  obtain ⟨m, z, hz⟩ := IsLocalization.Away.surj a s
  have haS : IsUnit (algebraMap A S a ^ m) :=
    (IsLocalization.Away.algebraMap_isUnit a).pow _
  have hz₀ : z ≠ 0 := fun h => hs (haS.mul_left_inj.mp (by simpa [h] using hz))
  refine ⟨a * z, mul_ne_zero ha₀ hz₀, ?_⟩
  intro F _ _ hr
  rw [map_mul, mul_ne_zero_iff] at hr
  let sF : S →+* F := IsLocalization.Away.lift a (isUnit_iff_ne_zero.mpr hr.1)
  let : Algebra S F := sF.toAlgebra
  let : IsScalarTower A S F := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.Away.lift_eq a _ x).symm
  have hsF : algebraMap S F s ≠ 0 := by
    intro h
    have hzF := congrArg (algebraMap S F) hz
    rw [map_mul, h, zero_mul, ← IsScalarTower.algebraMap_apply A S F] at hzF
    exact hr.2 hzF.symm
  let : IsDomain (F ⊗[S] B') := hOpen F hsF
  let eF := Algebra.TensorProduct.cancelBaseChange A S F F B
  exact Function.Injective.isDomain eF.symm.toRingHom eF.symm.injective

end SerrePositivity.AlgebraicGeometry
