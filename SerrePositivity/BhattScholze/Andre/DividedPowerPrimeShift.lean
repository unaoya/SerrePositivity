module

public import SerrePositivity.BhattScholze.RankOneDPAnyBasis
public import SerrePositivity.BhattScholze.RankOneDPPrimeBlocks
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Algebra.Algebra.Bilinear

/-!
# André E1・E2：標数 p の一元分冪代数の素数次数シフト

## 概要

p が零となる係数環上の一元分冪代数には γₙ を γₚₙ へ送る係数代数射がある。
その反復により、各 γₚⁱ の p 乗は零となる。
BS Rem 7.15(1)（著者版 p.62）の切断多項式表示の関係式の計算。

## 方針

具体的な分冪基底から線形写像を定める。二項係数の Lucas 合同により積を保存する。
一次分冪生成元の p 乗消滅をこの代数射で順に移す。

## 規約

p は素数とする。係数環の非零性や CharP の型クラスは要求せず、p=0 を明示する。
実 pd 包や prismatic envelope の同定は別工程。

## 使われ方

可算個の切断変数を分冪代数へ評価する射の関係式を供給する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "DA" => DividedPowerAlgebra A A
local notation "b" => rankOneDPAnyBasis A

omit [Fact p.Prime] in
/-- 概要：p が零となる環では、p に関する自然数の合同は係数環内の等式を与える。
方針：両自然数を剰余と p 倍に分ける。
規約：零環を含め、CharP のインスタンスを要求しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の Lucas 合同による積の照合。 -/
theorem natCast_eq_of_modEq_of_prime_zero (hp : (p : A) = 0) {m n : ℕ}
    (h : Nat.ModEq p m n) : (m : A) = (n : A) := by
  have hc (k : ℕ) : (k : A) = (k % p : ℕ) := by
    have he := congrArg (Nat.cast : ℕ → A) (Nat.mod_add_div k p)
    simpa only [Nat.cast_add, Nat.cast_mul, hp, zero_mul, add_zero] using he.symm
  exact (hc m).trans ((congrArg (Nat.cast : ℕ → A) h).trans (hc n).symm)

/-- 概要：標準分冪基底の次数を p 倍する係数線形写像。
方針：具体的基底からの線形写像の普遍性を使う。
規約：線形写像の定義自体には標数条件を使わない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の素数冪生成元。 -/
def dividedPowerPrimeShiftLinear : DA →ₗ[A] DA :=
  (b).constr A (fun n => DividedPowerAlgebra.dp A (p * n) (1 : A))

omit [Fact p.Prime] in
/-- 概要：次数シフト線形写像は γₙ を γₚₙ に送る。
方針：基底から定めた線形写像の基底上の公式を使う。
規約：標数条件は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の積の計算。 -/
theorem dividedPowerPrimeShiftLinear_dp (n : ℕ) :
    dividedPowerPrimeShiftLinear (A := A) p (DividedPowerAlgebra.dp A n (1 : A)) =
      DividedPowerAlgebra.dp A (p * n) (1 : A) := by
  simpa only [dividedPowerPrimeShiftLinear, rankOneDPAnyBasis_apply] using
    (b).constr_basis A (fun k => DividedPowerAlgebra.dp A (p * k) (1 : A)) n

/-- 概要：p が係数環内で零なら次数シフトは積を保存する。
方針：双線形写像を分冪基底上で比較し、Lucas の二項係数合同を使う。
規約：係数環の非零性は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の切断生成元への代数射。 -/
theorem dividedPowerPrimeShiftLinear_mul (hp : (p : A) = 0) (x y : DA) :
    dividedPowerPrimeShiftLinear p (x * y) =
      dividedPowerPrimeShiftLinear p x * dividedPowerPrimeShiftLinear p y := by
  let L := dividedPowerPrimeShiftLinear (A := A) p
  have hpD : (p : DA) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (algebraMap A DA) hp
  have hmul : (LinearMap.mul A DA).compr₂ L = (LinearMap.mul A DA).compl₁₂ L L := by
    apply (b).ext
    intro m
    apply (b).ext
    intro n
    change L ((b) m * (b) n) = L ((b) m) * L ((b) n)
    dsimp only [L]
    simp only [rankOneDPAnyBasis_apply, DividedPowerAlgebra.dp_mul, map_nsmul,
      dividedPowerPrimeShiftLinear_dp]
    have hc : (((p * (m + n)).choose (p * m) : ℕ) : DA) = ((m + n).choose m : ℕ) :=
      natCast_eq_of_modEq_of_prime_zero p hpD Choose.choose_mul_mul_modEq_choose_nat
    simp only [← Nat.mul_add]
    rw [nsmul_eq_mul, nsmul_eq_mul, hc]
  exact congrArg (fun f : DA →ₗ[A] DA →ₗ[A] DA => f x y) hmul

/-- 概要：標数 p の次数シフトを係数代数射として束ねる。
方針：線形写像の積保存、零次分冪と係数スカラーの保存を使う。
規約：係数環の p=0 を明示する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の素数冪次数の関係式。 -/
def dividedPowerPrimeShift (hp : (p : A) = 0) : DA →ₐ[A] DA where
  toFun := dividedPowerPrimeShiftLinear (A := A) p
  map_zero' := map_zero (dividedPowerPrimeShiftLinear (A := A) p)
  map_add' := map_add (dividedPowerPrimeShiftLinear (A := A) p)
  map_one' := by
    simpa only [Nat.mul_zero, DividedPowerAlgebra.dp_zero] using
      dividedPowerPrimeShiftLinear_dp (A := A) p 0
  map_mul' := dividedPowerPrimeShiftLinear_mul p hp
  commutes' a := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul]
    have h1 : dividedPowerPrimeShiftLinear p (1 : DA) = 1 := by
      simpa only [Nat.mul_zero, DividedPowerAlgebra.dp_zero] using
        dividedPowerPrimeShiftLinear_dp (A := A) p 0
    rw [h1]

/-- 概要：次数シフト代数射も、標準分冪生成元の次数を p 倍する。
方針：元の線形写像の公式を使う。
規約：係数環内で p は零。
使われ方：BS Rem 7.15(1)（著者版 p.62）の素数冪生成元の反復。 -/
theorem dividedPowerPrimeShift_dp (hp : (p : A) = 0) (n : ℕ) :
    dividedPowerPrimeShift p hp (DividedPowerAlgebra.dp A n (1 : A)) =
      DividedPowerAlgebra.dp A (p * n) (1 : A) :=
  dividedPowerPrimeShiftLinear_dp p n

/-- 概要：素数冪次数の分冪生成元 γₚⁿ の p 乗は零。
方針：一次生成元の p 乗消滅を次数シフト代数射で帰納的に移す。
規約：係数環の非零性を仮定しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の gᵢᵖ=0 の具体的関係。 -/
theorem dividedPowerPrimePower_pow_zero (hp : (p : A) = 0) (n : ℕ) :
    DividedPowerAlgebra.dp A (p ^ n) (1 : A) ^ p = 0 := by
  induction n with
  | zero =>
      simpa only [pow_zero] using rankOneDPGenerator_pow_eq_zero (Fact.out : p.Prime).pos hp
  | succ n ih =>
      have h := congrArg (dividedPowerPrimeShift p hp) ih
      rw [map_pow, dividedPowerPrimeShift_dp, map_zero] at h
      simpa only [pow_succ'] using h

/-- 概要：素数次数のシフト線形写像は単射。
方針：標準分冪基底の線形独立性を、単射な指数写像 n↦pn に沿って制限する。
規約：この単射性には係数環内の p=0 は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の切断多項式表示の独立性の準備。 -/
theorem dividedPowerPrimeShiftLinear_injective :
    Function.Injective (dividedPowerPrimeShiftLinear (A := A) p) := by
  have hi : Function.Injective (fun n : ℕ => p * n) := by
    intro m n h
    exact Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos h
  change Function.Injective ((b).constr A
    (fun n => DividedPowerAlgebra.dp A (p * n) (1 : A)))
  apply (b).injective_constr_of_linearIndependent
  simpa only [rankOneDPAnyBasis_apply, Function.comp_def] using (b).linearIndependent.comp _ hi

/-- 概要：標数 p の素数次数シフト代数射は単射。
方針：同じ台写像の係数線形単射性を使う。
規約：係数環の非零性は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の素数冪生成元の独立性。 -/
theorem dividedPowerPrimeShift_injective (hp : (p : A) = 0) :
    Function.Injective (dividedPowerPrimeShift (A := A) p hp) :=
  dividedPowerPrimeShiftLinear_injective p

end SerrePositivity.BhattScholze.Andre
