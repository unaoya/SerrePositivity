module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Integral

/-!
概要：素点の剰余体上で整な有限個の座標は、素点を含む一つの主開上で整になる。
方針：局所環にモニック方程式を持ち上げ、座標の分母を一つの積で払う。
規約：座標の値を取る体の代数構造は、指定した剰余体を経由する。
使われ方：初等 étale 近傍で有限平坦な標識を構成する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open Polynomial

/--
概要：素点の剰余体上で整な有限個の座標は、基底を一つの主開に縮めると整になる。
方針：基底の局所環でモニック方程式を取り、共通の分母を反転する。
規約：得られる座標の評価写像は、元の基底代数の構造と両立する。
使われ方：アフィン空間への étale チャートの有限自由な切断。
-/
theorem exists_away_integral_of_isIntegral_residueField
    {R F ι : Type*} [CommRing R] [Field F] [Finite ι] (p : Ideal R) [p.IsPrime]
    [Algebra R F] [Algebra p.ResidueField F] [IsScalarTower R p.ResidueField F]
    (x : ι → F) (hx : ∀ i, IsIntegral p.ResidueField (x i)) :
    ∃ (a : R) (_ : a ∉ p) (j : Localization.Away a →ₐ[R] F),
      letI : Algebra (Localization.Away a) F := j.toRingHom.toAlgebra
      ∀ i, IsIntegral (Localization.Away a) (x i) := by
  classical
  let k := p.ResidueField
  let L := Localization.AtPrime p
  let : Algebra L F := ((algebraMap k F).comp (algebraMap L k)).toAlgebra
  let : IsScalarTower L k F := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R L F := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R F r = algebraMap k F (algebraMap L k (algebraMap R L r))
    rw [← IsScalarTower.algebraMap_apply R L k, ← IsScalarTower.algebraMap_apply R k F]
  have hL (i : ι) : IsIntegral L (x i) := by
    obtain ⟨f, hf, hfx⟩ := hx i
    have hLift : f ∈ Polynomial.lifts (algebraMap L k) :=
      Polynomial.mem_lifts_of_surjective (IsLocalRing.residue_surjective (R := L)) f
    obtain ⟨g, hg, _, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hLift hf
    refine ⟨g, hgm, ?_⟩
    change g.eval₂ (algebraMap L F) (x i) = 0
    rw [IsScalarTower.algebraMap_eq L k F, ← Polynomial.eval₂_map, hg]
    exact hfx
  choose d hd using fun i => IsIntegral.exists_multiple_integral_of_isLocalization
    (Rₘ := L) p.primeCompl (x i) (hL i)
  let : Fintype ι := Fintype.ofFinite ι
  let a := ∏ i, (d i : R)
  have ha : a ∉ p := by
    change a ∈ p.primeCompl
    exact p.primeCompl.prod_mem fun i _ => (d i).2
  have hax (i : ι) : IsIntegral R (a • x i) := by
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun i => (d i : R)) (Finset.mem_univ i)
    rw [show a = (d i : R) * r from hr, mul_comm, mul_smul]
    exact (hd i).smul r
  have hUnit : IsUnit (algebraMap R F a) := isUnit_iff_ne_zero.mpr fun h =>
    ha (Ideal.algebraMap_residueField_eq_zero.mp
      ((RingHom.injective (algebraMap k F)) (by
        rw [← IsScalarTower.algebraMap_apply R k F, map_zero]
        exact h)))
  let A := Localization.Away a
  let j : A →ₐ[R] F := IsLocalization.Away.liftAlgHom a (f := Algebra.ofId R F) hUnit
  let : Algebra A F := j.toRingHom.toAlgebra
  let : IsScalarTower R A F := IsScalarTower.of_algebraMap_eq' j.comp_algebraMap.symm
  refine ⟨a, ha, j, fun i => ?_⟩
  let u : Aˣ := (IsLocalization.Away.algebraMap_isUnit (S := A) a).unit
  have hu : (u : A) = algebraMap R A a := IsUnit.unit_spec _
  have hi : IsIntegral A ((↑(u⁻¹) : A) • (a • x i)) :=
    (IsIntegral.tower_top (A := A) (hax i)).smul _
  rwa [← IsScalarTower.algebraMap_smul A a (x i), ← hu, smul_smul, Units.inv_mul, one_smul] at hi

end SerrePositivity.AlgebraicGeometry
