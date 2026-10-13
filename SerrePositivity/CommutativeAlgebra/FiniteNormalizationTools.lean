module

public import SerrePositivity.CommutativeAlgebra.FiniteLocalSupport
public import SerrePositivity.CommutativeAlgebra.IntegralDimension
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-! # 有限正規化の閉ファイバーと単射性

指定剰余体への全射性と準素性から閉ファイバーの有限性を供給する。
有限な環写像の単射性は、整域の非零元による次元降下と次元の一致から導く。
-/

public section
universe u
namespace SerrePositivity
open IsLocalRing

/-- 指定剰余体へ全射な係数環上では、極大イデアル準素商は有限加群。 -/
theorem finite_quotient_of_common_residue_primary
    {A D : Type u} [CommRing A] [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    [Algebra A D] (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    (J : Ideal D) (hJ : J.radical = maximalIdeal D) : Module.Finite A (D ⧸ J) := by
  have hJtop : J ≠ ⊤ := by
    intro h
    rw [h, Ideal.radical_top] at hJ
    exact (maximalIdeal.isMaximal D).ne_top hJ.symm
  let : Nontrivial (D ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  let : IsLocalRing (D ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let : IsNoetherianRing (D ⧸ J) :=
    isNoetherianRing_of_surjective D _ (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let : IsArtinianRing (D ⧸ maximalIdeal D) :=
    inferInstanceAs (IsArtinianRing (ResidueField D))
  let : IsArtinianRing (D ⧸ J) :=
    isArtinianRing_quotient_of_le_radical (maximalIdeal D) J (hJ ▸ le_rfl)
  have hres' : Function.Surjective ((residue (D ⧸ J)).comp (algebraMap A (D ⧸ J))) :=
    residue_surjective_comp_of_surjective (algebraMap A D) (Ideal.Quotient.mk J)
      hres Ideal.Quotient.mk_surjective
  have hlen : Module.length A (D ⧸ J) ≠ ⊤ := by
    rw [length_eq_of_common_residueField hres' (D ⧸ J)]
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
  let : IsNoetherian A (D ⧸ J) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hlen)).1
  infer_instance

/-- 有限次元の整域を始域とする有限写像は、次元が一致すれば単射。
終域の整域性・局所性、始域の正則性・局所性は不要。 -/
theorem ringHom_injective_of_finite_of_equal_dimension
    {A D : Type*} [CommRing A] [IsDomain A] [CommRing D]
    (f : A →+* D) (hf : f.Finite) {h : ℕ}
    (hA : ringKrullDim A = h) (hD : ringKrullDim D = h) : Function.Injective f := by
  let : Algebra A D := f.toAlgebra
  let : Module.Finite A D := hf
  let K := RingHom.ker f
  let g : A ⧸ K →+* D := Ideal.Quotient.lift K f (fun _ hx ↦ hx)
  let : Algebra (A ⧸ K) D := g.toAlgebra
  let : IsScalarTower A (A ⧸ K) D := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let : Module.Finite (A ⧸ K) D := Module.Finite.of_restrictScalars_finite A _ _
  have hd : ringKrullDim D ≤ ringKrullDim (A ⧸ K) := ringKrullDim_le_of_integral _ _
  apply (RingHom.injective_iff_ker_eq_bot f).mpr
  apply le_antisymm ?_ bot_le
  intro x hx
  by_contra hx0
  have hxne : x ≠ 0 := hx0
  have hspan : Ideal.span {x} ≤ K := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact hx
  have hq : ringKrullDim (A ⧸ K) ≤ ringKrullDim (A ⧸ Ideal.span {x}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hspan)
      (Ideal.Quotient.factor_surjective hspan)
  have hdrop := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_iff_ne_zero.mpr hxne)
  have hle : ringKrullDim D + 1 ≤ ringKrullDim (A ⧸ Ideal.span {x}) + 1 :=
    add_le_add (hd.trans hq) le_rfl
  have hbad := hle.trans hdrop
  rw [hA, hD] at hbad
  have : h + 1 ≤ h := by exact_mod_cast hbad
  omega

end SerrePositivity
