module

public import SerrePositivity.FieldTheory.AdjoinSingletonDifferential
public import SerrePositivity.FieldTheory.PAdjoinDerivation

/-! # p 乗根の添加での Kähler 微分の次元

概要：p 乗根 `x`（`x ^ p = a`、`x ∉ K`）が `L` を生成するとき、
`ker (L ⊗_K Ω_{K/R} → Ω_{L/R})` は `1 ⊗ D a` の張る直線であり、`D a ≠ 0` なら `dim Ω_{L/R} = dim Ω_{K/R}`。
方針：一元生成の非分離拡大の一般論（`AdjoinSingletonDifferential`）に、最小多項式 `X ^ p - a` の関係式の微分が
`-(1 ⊗ D a)` であることを代入する。
使われ方：共有限な部分体族での次数 p の階数安定（`SubfieldFamilyDifferentialRank`）。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open Polynomial
open scoped TensorProduct

variable {R K L : Type*} [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
variable {p : ℕ} [Fact p.Prime] [CharP L p]

/-- p 乗根の関係式 `X ^ p - a` の微分は `-(1 ⊗ D a)`。 -/
theorem relationDifferential_primeRoot (x : L) (a : K) (hpow : x ^ p = algebraMap K L a)
    (hx : x ∉ Set.range (algebraMap K L)) :
    relationDifferential R x = -((1 : L) ⊗ₜ[K] KaehlerDifferential.D R K a) := by
  rw [relationDifferential, minpoly_eq_X_pow_sub_C_of_pow_eq x a hpow hx, map_sub,
    coefficientEvalLinearMap_C, ← monomial_one_right_eq_X_pow]
  simp [coefficientEvalLinearMap]

/-- 非自明なp乗根が終域を生成するとき、推移列の核は関係式の微分の一方向。 -/
theorem ker_mapBaseChange_primeRoot_of_adjoin_eq_top (x : L) (a : K)
    (hpow : x ^ p = algebraMap K L a) (hx : x ∉ Set.range (algebraMap K L))
    (hs : Algebra.adjoin K {x} = ⊤) :
    LinearMap.ker (KaehlerDifferential.mapBaseChange R K L) =
      L ∙ ((1 : L) ⊗ₜ[K] KaehlerDifferential.D R K a) := by
  rw [ker_mapBaseChange_of_adjoin_singleton x hs
      (derivative_minpoly_eq_zero_of_prime_pow_eq x a hpow hx),
    relationDifferential_primeRoot x a hpow hx, ← Set.neg_singleton, Submodule.span_neg]

/-- 関係式の微分が非零なら、次数pの添加で通常微分の次元は変わらない。 -/
theorem finrank_kaehlerDifferential_primeRoot_tower_eq_of_adjoin_eq_top
    (F : Type*) [Field F] [Algebra F K] [Algebra F L] [IsScalarTower F K L]
    [Module.Finite F K] (x : L) (a : K) (hpow : x ^ p = algebraMap K L a)
    (hx : x ∉ Set.range (algebraMap K L)) (hs : Algebra.adjoin K {x} = ⊤)
    (ha : KaehlerDifferential.D F K a ≠ 0) :
    Module.finrank L (KaehlerDifferential F L) =
      Module.finrank K (KaehlerDifferential F K) := by
  let : Module.Finite K L :=
    (PowerBasis.ofAdjoinEqTop (isIntegral_of_prime_pow_eq x a hpow) hs).finite
  refine finrank_kaehlerDifferential_eq_of_adjoin_singleton F x hs
    (derivative_minpoly_eq_zero_of_prime_pow_eq x a hpow hx) ?_
  rw [relationDifferential_primeRoot x a hpow hx, neg_ne_zero]
  intro hz
  exact ha ((Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := K) (A := L)
    (KaehlerDifferential F K) (KaehlerDifferential.D F K a)).mp hz)

/-- 一つの底環S上で確認した非零性は、より小さい共有限な底体での次元等号にも使える。 -/
theorem finrank_kaehlerDifferential_primeRoot_tower_eq_of_baseRestriction
    (F S : Type*) [Field F] [CommRing S]
    [Algebra F S] [Algebra F K] [Algebra S K] [IsScalarTower F S K]
    [Algebra F L] [IsScalarTower F K L] [Module.Finite F K]
    (x : L) (a : K) (hpow : x ^ p = algebraMap K L a)
    (hx : x ∉ Set.range (algebraMap K L)) (hs : Algebra.adjoin K {x} = ⊤)
    (ha : KaehlerDifferential.D S K a ≠ 0) :
    Module.finrank L (KaehlerDifferential F L) =
      Module.finrank K (KaehlerDifferential F K) :=
  finrank_kaehlerDifferential_primeRoot_tower_eq_of_adjoin_eq_top F x a hpow hx hs
    fun h ↦ ha (by simpa only [KaehlerDifferential.map_D, Algebra.algebraMap_self,
      RingHom.id_apply, map_zero] using congrArg (KaehlerDifferential.map F S K K) h)

end SerrePositivity
