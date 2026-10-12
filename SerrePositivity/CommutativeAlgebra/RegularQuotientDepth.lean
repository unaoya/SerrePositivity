module

public import SerrePositivity.CommutativeAlgebra.RegularParameters
public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.Regular.Category

/-! # 正則列による商の深さの下界

正則元による短完全列の深さ補題から、弱正則列による商では深さが列の長さ以上には
減少しないことを、拡大自然数の加法的な不等式として示す。正則局所環には次元と同数の
正則な極大イデアル生成元があるので、その商の深さと列の長さの和は元の次元以上である。
非混合性の未証明入力は使わない。
-/

@[expose] public section

universe u

open IsLocalRing RingTheory.Sequence CategoryTheory

namespace SerrePositivity.RegularQuotientDepth

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- 正則元による商では深さは高々一つしか下がらない。零加群・無限深さも含む。 -/
theorem depth_le_depth_quotSMulTop_add_one
    (M : Type u) [AddCommGroup M] [Module R M] (x : R) (hx : IsSMulRegular M x) :
    IsLocalRing.depth (ModuleCat.of R M) ≤
      IsLocalRing.depth (ModuleCat.of R (QuotSMulTop x M)) + 1 := by
  let N := ModuleCat.of R (Shrink.{u} (R ⧸ maximalIdeal R))
  have h := ModuleCat.depth_min_snd_fst_sub_one_le_trd_right N
    ((ModuleCat.of R M).smulShortComplex x) hx.smulShortComplex_shortExact
  change IsLocalRing.depth (ModuleCat.of R M) ⊓
      (IsLocalRing.depth (ModuleCat.of R M) - 1) ≤
    IsLocalRing.depth (ModuleCat.of R (QuotSMulTop x M)) at h
  rw [inf_of_le_right tsub_le_self] at h
  exact tsub_le_iff_right.mp h

/-- 弱正則列による商の深さと列の長さの和は、元の加群の深さ以上である。
有限生成性・Noether 性を要求しない。 -/
theorem depth_le_depth_quotient_add_length
    (M : Type u) [AddCommGroup M] [Module R M]
    (rs : List R) (hrs : IsWeaklyRegular M rs) :
    IsLocalRing.depth (ModuleCat.of R M) ≤
      IsLocalRing.depth (ModuleCat.of R
        (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M))) + rs.length := by
  induction rs generalizing M with
  | nil =>
      rw [Ideal.ofList_nil, Submodule.bot_smul, List.length_nil, Nat.cast_zero, add_zero]
      exact (IsLocalRing.depth_eq_of_linearEquiv
        (Submodule.quotEquivOfEqBot (⊥ : Submodule R M) rfl)).symm.le
  | cons x rs ih =>
      obtain ⟨hx, htail⟩ := (isWeaklyRegular_cons_iff M x rs).mp hrs
      have hstep := depth_le_depth_quotSMulTop_add_one M x hx
      have hnext : IsLocalRing.depth (ModuleCat.of R (QuotSMulTop x M)) + 1 ≤
          (IsLocalRing.depth (ModuleCat.of R
            (QuotSMulTop x M ⧸ (Ideal.ofList rs • ⊤ : Submodule R (QuotSMulTop x M)))) +
            rs.length) + 1 := add_le_add (ih (QuotSMulTop x M) htail) le_rfl
      have h := hstep.trans hnext
      rw [← IsLocalRing.depth_eq_of_linearEquiv
        (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs)] at h
      simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc] using h

/-- proper な生成イデアルの生成列の各元は、極大イデアルに入る。 -/
theorem mem_maximalIdeal_of_mem_ofList_ne_top (rs : List R)
    (hproper : Ideal.ofList rs ≠ ⊤) {x : R} (hx : x ∈ rs) :
    x ∈ maximalIdeal R :=
  le_maximalIdeal hproper (Ideal.subset_span hx)

omit [IsLocalRing R] in
/-- 自己加群上の弱正則列は、その生成イデアルが proper なら正則列である。 -/
theorem isRegular_of_isWeaklyRegular_of_ofList_ne_top (rs : List R)
    (hrs : IsWeaklyRegular R rs) (hproper : Ideal.ofList rs ≠ ⊤) : IsRegular R rs := by
  refine ⟨hrs, ?_⟩
  change (⊤ : Ideal R) ≠ Ideal.ofList rs • ⊤
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  exact hproper.symm

omit [IsLocalRing R] in
/-- 非零の商を持つ自己加群上の弱正則列は正則列である。 -/
theorem isRegular_of_isWeaklyRegular_of_quotient_nontrivial (rs : List R)
    (hrs : IsWeaklyRegular R rs) [Nontrivial (R ⧸ Ideal.ofList rs)] : IsRegular R rs :=
  isRegular_of_isWeaklyRegular_of_ofList_ne_top rs hrs
    (Ideal.Quotient.nontrivial_iff.mp inferInstance)

/-- 正則局所環の深さは Krull 次元以上である。最小正則生成列の存在から従う。 -/
theorem dimToNat_le_depth (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    (dimToNat (ringKrullDim R) : ℕ∞) ≤ IsLocalRing.depth (ModuleCat.of R R) := by
  obtain ⟨rs, hrs, hgen, hdim⟩ := exists_regular_generators R
  have hproper : Ideal.ofList rs ≠ ⊤ := hgen ▸ (maximalIdeal.isMaximal R).ne_top
  have hreg := isRegular_of_isWeaklyRegular_of_ofList_ne_top rs hrs hproper
  have hmem : ∀ x ∈ rs, x ∈ maximalIdeal R :=
    fun x hx ↦ mem_maximalIdeal_of_mem_ofList_ne_top rs hproper hx
  have hlen : dimToNat (ringKrullDim R) = rs.length := by
    rw [hdim]
    simp [dimToNat]
  rw [hlen, IsLocalRing.depth_eq_sSup_length_isRegular]
  exact le_sSup ⟨rs, hreg, hmem, rfl⟩

/-- 非混合性の適用で必要になる、正則列商の深さの次元による下界。 -/
theorem dimToNat_le_depth_ringQuotient_add_length
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (rs : List R) (hrs : IsWeaklyRegular R rs) :
    (dimToNat (ringKrullDim R) : ℕ∞) ≤
      IsLocalRing.depth (ModuleCat.of R (R ⧸ Ideal.ofList rs)) + rs.length := by
  have h := (dimToNat_le_depth R).trans (depth_le_depth_quotient_add_length R rs hrs)
  have heq : (Ideal.ofList rs • ⊤ : Submodule R R) = Ideal.ofList rs := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  rwa [heq] at h

end SerrePositivity.RegularQuotientDepth
