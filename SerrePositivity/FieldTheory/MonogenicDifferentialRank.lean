module

public import SerrePositivity.FieldTheory.PAdjoinDerivation
public import SerrePositivity.CommutativeAlgebra.DerivationSpan
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.TensorProduct.Finite

/-! # 単生成の非分離拡大の通常微分

最小多項式の微分が零なら、生成元の微分が通常相対微分の一元基底になる。
p乗根の添加に適用し、階数安定化の純非分離段階に必要な推移列の次元式を供給する。
核の一方向への同定と次元の等号はPrimeRootDifferentialKernelで扱う。
部分体の選択と階数安定化全体は、ここでは主張しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open Polynomial
open scoped TensorProduct
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- 冪基底の生成元の微分が、通常相対微分の全体を張る。 -/
theorem _root_.PowerBasis.span_kaehlerDifferential_gen (B : PowerBasis K L) :
    Submodule.span L {KaehlerDifferential.D K L B.gen} = ⊤ := by
  simpa only [Set.image_singleton] using
    span_kaehlerDifferential_of_adjoin_eq_top {B.gen} B.adjoin_gen_eq_top

/-- 非分離な単生成拡大の、生成元の微分からなる実際の一元基底。 -/
def _root_.PowerBasis.kaehlerDifferentialBasis (B : PowerBasis K L)
    (h : derivative (minpoly K B.gen) = 0) :
    Module.Basis Unit L (KaehlerDifferential K L) :=
  Module.Basis.mk
    (v := fun _ : Unit ↦ KaehlerDifferential.D K L B.gen)
    (linearIndependent_unique_iff.mpr (B.kaehlerDifferential_gen_ne_zero h))
    (by simpa only [Set.range_const] using B.span_kaehlerDifferential_gen.ge)

@[simp] theorem _root_.PowerBasis.kaehlerDifferentialBasis_apply (B : PowerBasis K L)
    (h : derivative (minpoly K B.gen) = 0) (i : Unit) :
    B.kaehlerDifferentialBasis h i = KaehlerDifferential.D K L B.gen :=
  Module.Basis.mk_apply _ _ _

/-- 非分離な単生成拡大の通常相対微分の次元は1。 -/
theorem _root_.PowerBasis.finrank_kaehlerDifferential (B : PowerBasis K L)
    (h : derivative (minpoly K B.gen) = 0) :
    Module.finrank L (KaehlerDifferential K L) = 1 := by
  simpa using Module.finrank_eq_card_basis (B.kaehlerDifferentialBasis h)

/-- 実際に終域全体を生成する非自明なp乗根添加の相対微分の次元。 -/
theorem finrank_kaehlerDifferential_primeRoot_of_adjoin_eq_top
    {p : ℕ} [Fact p.Prime] [CharP L p] (x : L) (a : K)
    (hpow : x ^ p = algebraMap K L a) (hx : x ∉ Set.range (algebraMap K L))
    (hs : Algebra.adjoin K {x} = ⊤) :
    Module.finrank L (KaehlerDifferential K L) = 1 := by
  let B := PowerBasis.ofAdjoinEqTop (isIntegral_of_prime_pow_eq x a hpow) hs
  apply B.finrank_kaehlerDifferential
  rw [PowerBasis.ofAdjoinEqTop_gen]
  exact derivative_minpoly_eq_zero_of_prime_pow_eq x a hpow hx

/-- 推移列の中項の次元は、元の体からの微分の像の次元に1を加えたもの。
有限性は有限体拡大から確認する。像の余次元の同定は別の課題。 -/
theorem _root_.PowerBasis.finrank_kaehlerDifferential_tower
    (R : Type*) [Field R] [Algebra R K] [Algebra R L] [IsScalarTower R K L]
    [Module.Finite R K] (B : PowerBasis K L) (h : derivative (minpoly K B.gen) = 0) :
    Module.finrank L (KaehlerDifferential R L) =
      Module.finrank L (LinearMap.range (KaehlerDifferential.mapBaseChange R K L)) + 1 := by
  let : Module.Finite K L := B.finite
  let : Module.Finite R L := Module.Finite.trans (R := R) K L
  have heq := LinearMap.finrank_range_add_finrank_ker (KaehlerDifferential.map R K L L)
  rw [LinearMap.range_eq_top.mpr (KaehlerDifferential.map_surjective R K L),
    finrank_top, B.finrank_kaehlerDifferential h,
    ← KaehlerDifferential.range_mapBaseChange R K L] at heq
  exact heq.symm.trans (Nat.add_comm _ _)

/-- p乗根の関係式の微分は、推移列の最初の写像の核に入る。 -/
theorem primeRoot_differential_mem_ker_mapBaseChange
    (R : Type*) [CommRing R] [Algebra R K] [Algebra R L] [IsScalarTower R K L]
    {p : ℕ} [CharP L p] (x : L) (a : K) (hpow : x ^ p = algebraMap K L a) :
    (1 : L) ⊗ₜ[K] KaehlerDifferential.D R K a ∈
      LinearMap.ker (KaehlerDifferential.mapBaseChange R K L) := by
  rw [LinearMap.mem_ker, KaehlerDifferential.mapBaseChange_tmul, one_smul,
    KaehlerDifferential.map_D, ← hpow]
  exact derivation_pow_char_eq_zero p (KaehlerDifferential.D R L) x

/-- 底体側の関係式の微分が非零なら、p乗根添加で微分の次元は増えない。
核に実際の非零元を供給して証明する。等号はPrimeRootDifferentialKernelで扱う。 -/
theorem _root_.PowerBasis.finrank_kaehlerDifferential_tower_le_of_primeRoot
    (R : Type*) [Field R] [Algebra R K] [Algebra R L] [IsScalarTower R K L]
    [Module.Finite R K] (B : PowerBasis K L)
    {p : ℕ} [CharP L p] (h : derivative (minpoly K B.gen) = 0)
    (a : K) (hpow : B.gen ^ p = algebraMap K L a)
    (ha : KaehlerDifferential.D R K a ≠ 0) :
    Module.finrank L (KaehlerDifferential R L) ≤
      Module.finrank K (KaehlerDifferential R K) := by
  let : Module.Finite K L := B.finite
  let : Module.Finite R L := Module.Finite.trans (R := R) K L
  have ht : (1 : L) ⊗ₜ[K] KaehlerDifferential.D R K a ≠ 0 := by
    intro hz
    exact ha ((Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := K) (A := L)
      (KaehlerDifferential R K) (KaehlerDifferential.D R K a)).mp hz)
  have hp : 0 < Module.finrank L
      (LinearMap.ker (KaehlerDifferential.mapBaseChange R K L)) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨_, primeRoot_differential_mem_ker_mapBaseChange R B.gen a hpow⟩, ?_⟩
    intro hz
    exact ht (congrArg Subtype.val hz)
  have hn := LinearMap.finrank_range_add_finrank_ker
    (KaehlerDifferential.mapBaseChange R K L)
  rw [Module.finrank_baseChange] at hn
  have hd := B.finrank_kaehlerDifferential_tower R h
  omega

/-- 非自明なp乗根が終域全体を生成する場合の、非零の関係式による次元の上界。 -/
theorem finrank_kaehlerDifferential_primeRoot_tower_le_of_adjoin_eq_top
    (R : Type*) [Field R] [Algebra R K] [Algebra R L] [IsScalarTower R K L]
    [Module.Finite R K] {p : ℕ} [Fact p.Prime] [CharP L p]
    (x : L) (a : K) (hpow : x ^ p = algebraMap K L a)
    (hx : x ∉ Set.range (algebraMap K L)) (hs : Algebra.adjoin K {x} = ⊤)
    (ha : KaehlerDifferential.D R K a ≠ 0) :
    Module.finrank L (KaehlerDifferential R L) ≤
      Module.finrank K (KaehlerDifferential R K) := by
  let B := PowerBasis.ofAdjoinEqTop (isIntegral_of_prime_pow_eq x a hpow) hs
  have hg : B.gen = x := PowerBasis.ofAdjoinEqTop_gen _ _
  apply B.finrank_kaehlerDifferential_tower_le_of_primeRoot R (a := a)
  · rw [hg]
    exact derivative_minpoly_eq_zero_of_prime_pow_eq x a hpow hx
  · simpa only [hg] using hpow
  · exact ha

end SerrePositivity
