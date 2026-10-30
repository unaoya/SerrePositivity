module

public import SerrePositivity.CommutativeAlgebra.Length.CommonResidueField
public import SerrePositivity.CommutativeAlgebra.IntegralDimension
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Jacobson.Ideal
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Eval
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Dimension
public import Mathlib.RingTheory.KrullDimension.Field

/-! # 有限正規化の一般的な道具

概要：完備局所環を冪級数環上に有限に表す（有限正規化）ときに使う一般論。
- 剰余体へ全射な係数環 `A → D`（`D` は Noether 局所）の上では、極大イデアルに準素な商 `D/J` は有限 `A` 加群。
- 有限次元の整域 `A` からの有限写像 `A → D` は、`dim A = dim D` なら単射。
- 生成元を正の冪にしても生成イデアルの根基は変わらない。冪級数の評価は変数のイデアルを像のイデアルへ送る。
方針：有限性は、`D/J` が Artin 局所で剰余体が係数環の像なので、長さが有限になることから。単射性は、核の非零元で
割ると次元が一つ下がる（Mathlib の `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`）ことと、整拡大で次元が増えないことから。
規約：標数・完備性・正則性は仮定しない。評価そのものは `PowerSeries/Eval` の `adicPowerSeriesEval` を使う。
使われ方：同標数の正規化（`EqualCharacteristicNormalization`）、混標数の Witt 正規化、完備微分の有限性、
中間係数体上の正規化（`CofiniteNormalization`）。
-/

@[expose] public section
namespace SerrePositivity

section Tools

universe u
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

end Tools

section PowerSeries

/-- 各生成元を正の冪に変えても、生成イデアルの根基は変わらない。 -/
theorem radical_span_powers {R σ : Type*} [CommRing R] (z : σ → R) (n : σ → ℕ)
    (hn : ∀ i, 0 < n i) :
    (Ideal.span (Set.range (fun i ↦ z i ^ n i))).radical = (Ideal.span (Set.range z)).radical := by
  apply le_antisymm
  · apply Ideal.radical_mono
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (Ideal.span (Set.range z)).pow_mem_of_mem
      (Ideal.subset_span (Set.mem_range_self i)) _ (hn i)
  · have hle : Ideal.span (Set.range z) ≤
        (Ideal.span (Set.range (fun i ↦ z i ^ n i))).radical := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨n i, Ideal.subset_span (Set.mem_range_self i)⟩
    simpa only [Ideal.radical_idem] using Ideal.radical_mono hle

/-- 変数の像を指定した環写像は、変数イデアルを指定族の生成イデアルへ送る。 -/
theorem map_powerSeries_variables_eq_span
    {k D σ : Type*} [CommRing k] [CommRing D]
    (F : MvPowerSeries σ k →+* D) (z : σ → D) (hX : ∀ i, F (MvPowerSeries.X i) = z i) :
    (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := k)))).map F =
      Ideal.span (Set.range z) := by
  rw [Ideal.map_span, ← Set.range_comp]
  congr 1
  exact congrArg Set.range (funext hX)

end PowerSeries

section Units

open IsLocalRing

/-- 各生成元の単元倍は、同じイデアルを生成する。 -/
theorem span_range_mul_units {S ι : Type*} [CommRing S]
    (z u : ι → S) (hu : ∀ i, IsUnit (u i)) :
    Ideal.span (Set.range (fun i ↦ z i * u i)) = Ideal.span (Set.range z) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_range_self i))
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨v, hv⟩ := hu i
    have h := Ideal.mul_mem_right (↑v⁻¹)
      (Ideal.span (Set.range (fun i ↦ z i * u i)))
      (Ideal.subset_span (Set.mem_range_self i))
    change z i ∈ Ideal.span (Set.range (fun i ↦ z i * u i))
    simpa only [← hv, mul_assoc, Units.val_mul, Units.mul_inv, Units.val_one, mul_one] using h

/-- 極大イデアル内の元を1に加えると単元となる。 -/
theorem isUnit_one_add_of_mem_maximalIdeal {S : Type*} [CommRing S] [IsLocalRing S]
    {f : S} (hf : f ∈ maximalIdeal S) : IsUnit (1 + f) :=
  Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (by
    rw [add_sub_cancel_left]
    exact maximalIdeal_le_jacobson ⊥ hf)

end Units

end SerrePositivity
