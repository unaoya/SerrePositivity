module

public import SerrePositivity.FieldTheory.PrimeRootDerivationExtension
public import SerrePositivity.FieldTheory.MonogenicDifferentialRank
public import SerrePositivity.CommutativeAlgebra.KaehlerBaseRestriction

/-! # p乗根添加の微分推移列の核

関係式の微分で割った加群への導分を実際に延長し、普遍性から核の逆包含を得る。
有限p-rank・微分空間の有限性は核の同定に要求しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open scoped TensorProduct
variable {R K L : Type*} [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]

/-- 非自明なp乗根が終域を生成するとき、推移列の核は関係式の微分の一方向。 -/
theorem ker_mapBaseChange_primeRoot_of_adjoin_eq_top
    {p : ℕ} [Fact p.Prime] [CharP L p] (x : L) (a : K)
    (hpow : x ^ p = algebraMap K L a) (hx : x ∉ Set.range (algebraMap K L))
    (hs : Algebra.adjoin K {x} = ⊤) :
    LinearMap.ker (KaehlerDifferential.mapBaseChange R K L) =
      L ∙ ((1 : L) ⊗ₜ[K] KaehlerDifferential.D R K a) := by
  let M := L ⊗[K] KaehlerDifferential R K
  let N : Submodule L M := L ∙ ((1 : L) ⊗ₜ[K] KaehlerDifferential.D R K a)
  let Q := M ⧸ N
  let : Module K Q := Module.compHom Q (algebraMap K L)
  let : Module R Q := Module.compHom Q (algebraMap R L)
  let : MulAction K Q := (Module.compHom Q (algebraMap K L)).toMulAction
  let : MulAction R Q := (Module.compHom Q (algebraMap R L)).toMulAction
  let : SMul K Q := (Module.compHom Q (algebraMap K L)).toSMul
  let : SMul R Q := (Module.compHom Q (algebraMap R L)).toSMul
  let : IsScalarTower K L Q :=
    IsScalarTower.of_algebraMap_smul (R := K) (A := L) (M := Q) fun _ _ ↦ rfl
  let : IsScalarTower R L Q :=
    IsScalarTower.of_algebraMap_smul (R := R) (A := L) (M := Q) fun _ _ ↦ rfl
  let : IsScalarTower R K Q :=
    IsScalarTower.of_algebraMap_smul (R := R) (A := K) (M := Q) fun r q ↦ by
      change algebraMap K L (algebraMap R K r) • q = algebraMap R L r • q
      rw [IsScalarTower.algebraMap_apply R K L]
  let i : KaehlerDifferential R K →ₗ[K] M :=
    TensorProduct.mk K L (KaehlerDifferential R K) 1
  let δ : Derivation R K Q := ((N.mkQ.restrictScalars K).comp i).compDer
    (KaehlerDifferential.D R K)
  have hδa : δ a = 0 := by
    change N.mkQ ((1 : L) ⊗ₜ[K] KaehlerDifferential.D R K a) = 0
    exact (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.mem_span_singleton_self _)
  obtain ⟨Δ, hΔ, _⟩ := exists_derivation_primeRoot_extension x a hpow hx hs δ hδa
  let F := Δ.liftKaehlerDifferential.comp (KaehlerDifferential.mapBaseChange R K L)
  have hi : (F.restrictScalars K).comp i = (N.mkQ.restrictScalars K).comp i := by
    apply Derivation.liftKaehlerDifferential_unique
    ext c
    change Δ.liftKaehlerDifferential
      (KaehlerDifferential.mapBaseChange R K L
        ((1 : L) ⊗ₜ[K] KaehlerDifferential.D R K c)) = δ c
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D,
      Derivation.liftKaehlerDifferential_comp_D, hΔ]
  have he : F = N.mkQ := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro l ω
    have hiω := congrArg (fun f : KaehlerDifferential R K →ₗ[K] Q ↦ f ω) hi
    change F ((1 : L) ⊗ₜ[K] ω) = N.mkQ ((1 : L) ⊗ₜ[K] ω) at hiω
    have ht : l ⊗ₜ[K] ω = l • ((1 : L) ⊗ₜ[K] ω) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht, map_smul, map_smul, hiω]
  apply le_antisymm
  · intro y hy
    have hz : N.mkQ y = 0 := by
      rw [← he]
      change Δ.liftKaehlerDifferential (KaehlerDifferential.mapBaseChange R K L y) = 0
      rw [show KaehlerDifferential.mapBaseChange R K L y = 0 from hy, map_zero]
    exact (Submodule.Quotient.mk_eq_zero N).mp hz
  · apply Submodule.span_le.mpr
    rintro y rfl
    exact primeRoot_differential_mem_ker_mapBaseChange R x a hpow

/-- 関係式の微分が非零なら、次数pの添加で通常微分の次元は変わらない。
共有限な底体R上の有限性を確認し、一方向の核と新しい一方向を計算する。 -/
theorem finrank_kaehlerDifferential_primeRoot_tower_eq_of_adjoin_eq_top
    (R : Type*) [Field R] [Algebra R K] [Algebra R L] [IsScalarTower R K L]
    [Module.Finite R K] {p : ℕ} [Fact p.Prime] [CharP L p]
    (x : L) (a : K) (hpow : x ^ p = algebraMap K L a)
    (hx : x ∉ Set.range (algebraMap K L)) (hs : Algebra.adjoin K {x} = ⊤)
    (ha : KaehlerDifferential.D R K a ≠ 0) :
    Module.finrank L (KaehlerDifferential R L) =
      Module.finrank K (KaehlerDifferential R K) := by
  let B := PowerBasis.ofAdjoinEqTop (isIntegral_of_prime_pow_eq x a hpow) hs
  let : Module.Finite K L := B.finite
  let : Module.Finite R L := Module.Finite.trans (R := R) K L
  have ht : (1 : L) ⊗ₜ[K] KaehlerDifferential.D R K a ≠ 0 := by
    intro hz
    exact ha ((Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := K) (A := L)
      (KaehlerDifferential R K) (KaehlerDifferential.D R K a)).mp hz)
  have hn := LinearMap.finrank_range_add_finrank_ker
    (KaehlerDifferential.mapBaseChange R K L)
  rw [Module.finrank_baseChange,
    ker_mapBaseChange_primeRoot_of_adjoin_eq_top (R := R) x a hpow hx hs,
    finrank_span_singleton ht] at hn
  have hd := LinearMap.finrank_range_add_finrank_ker (KaehlerDifferential.map R K L L)
  rw [LinearMap.range_eq_top.mpr (KaehlerDifferential.map_surjective R K L), finrank_top,
    finrank_kaehlerDifferential_primeRoot_of_adjoin_eq_top x a hpow hx hs,
    ← KaehlerDifferential.range_mapBaseChange R K L] at hd
  omega

/-- 一つの底環S上で確認した非零性は、より小さい共有限な底体Rでの次元等号にも使える。 -/
theorem finrank_kaehlerDifferential_primeRoot_tower_eq_of_baseRestriction
    (R S : Type*) [Field R] [CommRing S]
    [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    [Algebra R L] [IsScalarTower R K L] [Module.Finite R K]
    {p : ℕ} [Fact p.Prime] [CharP L p]
    (x : L) (a : K) (hpow : x ^ p = algebraMap K L a)
    (hx : x ∉ Set.range (algebraMap K L)) (hs : Algebra.adjoin K {x} = ⊤)
    (ha : KaehlerDifferential.D S K a ≠ 0) :
    Module.finrank L (KaehlerDifferential R L) =
      Module.finrank K (KaehlerDifferential R K) :=
  finrank_kaehlerDifferential_primeRoot_tower_eq_of_adjoin_eq_top R x a hpow hx hs
    (kaehlerDifferential_ne_zero_of_baseRestriction R S K a ha)

end SerrePositivity
