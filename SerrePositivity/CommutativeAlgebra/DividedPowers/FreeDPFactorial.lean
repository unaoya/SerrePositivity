module
public import SerrePositivity.CommutativeAlgebra.DividedPowers.FactorialCoefficients

public import SerrePositivity.CommutativeAlgebra.DividedPowers.FreeDPBasis
public import SerrePositivity.CommutativeAlgebra.DividedPowers.FactorialSubring
public import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# 自由変数の分冪代数と階乗部分環

## 概要
自由分冪代数を、多項式環の p 局所化内で変数の階乗分母が生成する部分環と同定する。

## 方針
係数の p 局所化上の多項式環へ分冪を評価し、分冪単項式と通常の多項式の生成元で像を比較する。

## 規約
係数環では p が正則で、p の倍数でない自然数の像が単元。

## 使われ方
変数に沿う分冪包と δ 環の除法表示の比較。
-/

public section
noncomputable section

universe u

namespace SerrePositivity.BhattScholze

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {p : ℕ} [Fact p.Prime] (S A : Type u) [CommRing A]
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))

local notation "T" => MvPolynomial S A
local notation "K" => Localization.Away (p : A)
local notation "L" => Localization.Away (p : T)
local notation "D" => DividedPowerAlgebra A (S →₀ A)
local notation "F" => pDivisionFactorialSubring p (MvPolynomial.X : S → T)

private def polynomialAwayEquiv : L ≃ₐ[T] MvPolynomial S K := by
  have hm : (Submonoid.powers (p : A)).map (MvPolynomial.C (σ := S)) =
      Submonoid.powers (p : T) := by
    rw [Submonoid.map_powers, MvPolynomial.C_eq_coe_nat]
  letI : IsLocalization (Submonoid.powers (p : T)) (MvPolynomial S K) :=
    hm ▸ MvPolynomial.isLocalization (σ := S) (Submonoid.powers (p : A)) K
  exact IsLocalization.algEquiv (Submonoid.powers (p : T)) L (MvPolynomial S K)

omit [Fact p.Prime] in
private theorem polynomialAwayEquiv_symm_X (s : S) :
    (polynomialAwayEquiv (p := p) S A).symm (MvPolynomial.X s) =
      algebraMap T L (MvPolynomial.X s) := by
  rw [← (polynomialAwayEquiv (p := p) S A).symm.commutes (MvPolynomial.X s)]
  rw [MvPolynomial.algebraMap_def, MvPolynomial.map_X]

private def freeDPToAway : D →ₐ[A] L :=
  letI := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
  (((polynomialAwayEquiv (p := p) S A).symm.restrictScalars A).toAlgHom).comp
    (freeDPPolynomialEval S A K)

private theorem freeDPToAway_dp (s : S) (n : ℕ) :
    freeDPToAway S A hlocal (DividedPowerAlgebra.dp A n (Finsupp.single s 1)) =
      pDivisionFactorialValue p (MvPolynomial.X : S → T) s n := by
  let := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
  change (polynomialAwayEquiv (p := p) S A).symm
    (freeDPPolynomialEval S A K (DividedPowerAlgebra.dp A n (Finsupp.single s 1))) = _
  rw [freeDPPolynomialEval_dp, map_mul, map_pow, polynomialAwayEquiv_symm_X]
  unfold pDivisionFactorialValue
  have h := (IsUnit.natCast_factorial_of_algebra ℚ n (A := K)).map_ringInverse
    (MvPolynomial.C : K →+* MvPolynomial S K)
  rw [map_natCast] at h
  simp only [h, map_ringInverse, map_natCast]

private theorem freeDPToAway_injective (hp : IsRegular (p : A)) :
    Function.Injective (freeDPToAway S A hlocal) := by
  let := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
  have ha : Function.Injective (algebraMap A K) := by
    apply (IsLocalization.injective_iff_isRegular (Submonoid.powers (p : A)) (S := K)).mpr
    rintro ⟨x, n, rfl⟩
    exact hp.pow n
  exact (polynomialAwayEquiv (p := p) S A).symm.injective.comp
    (freeDPPolynomialEval_injective S A K ha)

private theorem freeDPToAway_range :
    (freeDPToAway S A hlocal).toRingHom.range = F := by
  let f := freeDPToAway S A hlocal
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    have hz : z ∈ Submodule.span A (Set.range (freeDPMonomial S A)) := by
      rw [freeDPMonomial_span]
      trivial
    change f z ∈ F
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨m, rfl⟩ := hz
        simp only [f, freeDPMonomial, Finsupp.prod, map_prod, freeDPToAway_dp]
        exact Subring.prod_mem _ (fun s _ => pDivisionFactorialSubring_value_mem MvPolynomial.X s (m s))
    | zero =>
        rw [map_zero]
        exact Subring.zero_mem _
    | add x y _ _ hx hy =>
        rw [map_add]
        exact Subring.add_mem _ hx hy
    | smul a x _ hx =>
        rw [map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply A T L]
        exact Subring.mul_mem _ (pDivisionFactorialSubring_coeff_mem MvPolynomial.X _) hx
  · apply Subring.closure_le.mpr
    rintro _ (⟨q, rfl⟩ | ⟨⟨s, n⟩, rfl⟩)
    · change algebraMap T L q ∈ f.toRingHom.range
      induction q using MvPolynomial.induction_on with
      | C a =>
          refine ⟨algebraMap A D a, ?_⟩
          change f (algebraMap A D a) = _
          rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A T L, MvPolynomial.algebraMap_eq]
      | add q r hq hr =>
          rw [map_add]
          exact Subring.add_mem _ hq hr
      | mul_X q s hq =>
          rw [map_mul]
          refine Subring.mul_mem _ hq ⟨DividedPowerAlgebra.dp A 1 (Finsupp.single s 1), ?_⟩
          change freeDPToAway S A hlocal _ = _
          rw [freeDPToAway_dp, pDivisionFactorialValue, pow_one, Nat.factorial_one,
            Nat.cast_one, Ring.inverse_one, one_mul]
    · exact ⟨DividedPowerAlgebra.dp A n (Finsupp.single s 1), freeDPToAway_dp S A hlocal s n⟩

/-- 概要：自由分冪代数は変数の階乗分母が生成する p 局所化内の部分環に同型。
方針：有理係数への評価の単射性と生成元での像の計算を使う。
規約：p は係数環で正則で、p と素な自然数の像は単元。
使われ方：結晶側の変数分冪包の除法表示。 -/
def freeDPFactorialEquiv (hp : IsRegular (p : A)) : D ≃+* F :=
  (RingEquiv.ofBijective (freeDPToAway S A hlocal).toRingHom.rangeRestrict
    ⟨fun x y h => freeDPToAway_injective S A hlocal hp (congrArg Subtype.val h),
      fun z => by obtain ⟨x, hx⟩ := z.2; exact ⟨x, Subtype.ext hx⟩⟩).trans
    (RingEquiv.subringCongr (freeDPToAway_range S A hlocal))

/-- 比較同型は各変数の分冪を対応する階乗分母に送る。 -/
theorem freeDPFactorialEquiv_dp (hp : IsRegular (p : A)) (s : S) (n : ℕ) :
    (freeDPFactorialEquiv S A hlocal hp
      (DividedPowerAlgebra.dp A n (Finsupp.single s 1)) : L) =
      pDivisionFactorialValue p (MvPolynomial.X : S → T) s n := by
  unfold freeDPFactorialEquiv
  exact freeDPToAway_dp S A hlocal s n

/-- 比較同型は係数を多項式の定数として局所化へ送る。 -/
theorem freeDPFactorialEquiv_coeff (hp : IsRegular (p : A)) (a : A) :
    (freeDPFactorialEquiv S A hlocal hp (algebraMap A D a) : L) =
      algebraMap T L (MvPolynomial.C a) := by
  change freeDPToAway S A hlocal (algebraMap A D a) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A T L, MvPolynomial.algebraMap_eq]

open scoped TensorProduct in
/-- 概要：係数拡大した自由分冪代数と、拡大した係数の階乗部分環との比較同型。
方針：係数拡大同型と階乗部分環への評価を合成する。
規約：正則性と局所性は拡大後の係数環に課す。
使われ方：分冪変数と通常の多項式変数が共存する模型。 -/
def freeDPFactorialTensorEquiv (B : Type u) [CommRing B] [Algebra A B]
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B)) (hp : IsRegular (p : B)) :
    B ⊗[A] D ≃+* pDivisionFactorialSubring p (MvPolynomial.X : S → MvPolynomial S B) :=
  (freeDPBaseChangeEquiv S A B).toRingEquiv.trans (freeDPFactorialEquiv S B hB hp)

open scoped TensorProduct in
/-- 係数拡大との比較は分冪生成元を同じ変数の階乗分母へ送る。 -/
theorem freeDPFactorialTensorEquiv_dp (B : Type u) [CommRing B] [Algebra A B]
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B)) (hp : IsRegular (p : B))
    (s : S) (n : ℕ) :
    (freeDPFactorialTensorEquiv S A B hB hp
      (1 ⊗ₜ[A] DividedPowerAlgebra.dp A n (Finsupp.single s 1)) :
        Localization.Away (p : MvPolynomial S B)) =
      pDivisionFactorialValue p (MvPolynomial.X : S → MvPolynomial S B) s n := by
  have h (C : Type u) [CommRing C] :
      freeDPMonomial S C (Finsupp.single s n) =
        DividedPowerAlgebra.dp C n (Finsupp.single s 1) :=
    Finsupp.prod_single_index DividedPowerAlgebra.dp_zero
  rw [← h A, freeDPFactorialTensorEquiv, RingEquiv.trans_apply]
  change (freeDPFactorialEquiv S B hB hp (freeDPBaseChangeEquiv S A B _) :
    Localization.Away (p : MvPolynomial S B)) = _
  rw [freeDPBaseChangeEquiv_apply, freeDPBaseChangeMap_monomial, h B, freeDPFactorialEquiv_dp]

end SerrePositivity.BhattScholze
