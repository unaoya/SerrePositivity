module

public import SerrePositivity.BhattScholze.Andre.Remark715.DividedPowerPrimeShift
public import SerrePositivity.BhattScholze.Delta.DividedPower.RankOneDPPrimeBlockBasis
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.MonicPowerFamilyPresentation
public import Mathlib.RingTheory.Adjoin.Basic

/-!
# André E1・E2：素数冪分冪生成元と切断変数からの全射

## 概要

標数 p の一元分冪代数は全 γₚⁿ で係数代数として生成される。
各生成元の p 乗が零となることから、可算個の切断変数の多項式商から標準全射がある。
BS Rem 7.15(1)（著者版 p.62）の具体的表示への入力。

## 方針

次数シフトが生成部分代数を保つことと、次数の p 進商・剰余を使う強帰納を用いる。
p 未満の階乗が単元であることから、全ての標準分冪を生成する。

## 規約

ここでは切断変数からの全射までを示す。単射性や実 pd 包との同定は含まない。
係数環の非零性は不要。

## 使われ方

切断多項式表示の同型を構成する際の標準射と全射性を供給する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "DA" => DividedPowerAlgebra A A
local notation "S" => Algebra.adjoin A
  (Set.range fun n : ℕ => DividedPowerAlgebra.dp A (p ^ n) (1 : A))

/-- 概要：素数冪次数の分冪で生成した部分代数は次数シフトで保たれる。
方針：生成元・係数・和・積について確認する。
規約：標準次数シフト代数射を使う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の全分冪の生成の帰納。 -/
theorem dividedPowerPrimeShift_mem_adjoin (hp : (p : A) = 0) {x : DA} (hx : x ∈ S) :
    dividedPowerPrimeShift p hp x ∈ S := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨n, rfl⟩ := hx
      rw [dividedPowerPrimeShift_dp, ← pow_succ']
      exact Algebra.subset_adjoin (Set.mem_range_self (n + 1))
  | algebraMap a =>
      rw [AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy

/-- 概要：全ての標準分冪 γₙ は素数冪次数の分冪で生成した部分代数に属する。
方針：n の p による商・剰余と低次階乗の単元性を用いる強帰納。
規約：係数環の非零性を要求しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の切断変数表示への全射性。 -/
theorem dividedPower_dp_mem_prime_adjoin (hp : (p : A) = 0) (n : ℕ) :
    DividedPowerAlgebra.dp A n (1 : A) ∈ S := by
  have hprime := (Fact.out : p.Prime)
  have h1 : DividedPowerAlgebra.dp A 1 (1 : A) ∈ S :=
    Algebra.subset_adjoin ⟨0, rfl⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        simpa only [DividedPowerAlgebra.dp_zero] using (Subalgebra.one_mem S)
      · let k := n / p
        let r := n % p
        have hk : k < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hprime.one_lt
        have hr : r < p := Nat.mod_lt _ hprime.pos
        have he : p * k + r = n := by
          simpa only [k, r, Nat.mul_comm] using Nat.div_add_mod n p
        have hpk : DividedPowerAlgebra.dp A (p * k) (1 : A) ∈ S := by
          rw [← dividedPowerPrimeShift_dp p hp k]
          exact dividedPowerPrimeShift_mem_adjoin p hp (ih k hk)
        have hm := Subalgebra.mul_mem S (Subalgebra.pow_mem S h1 r) hpk
        rw [rankOneDPGenerator_pow_mul_prime_block hp, he] at hm
        have hs : (r.factorial : A) • DividedPowerAlgebra.dp A n (1 : A) ∈ (S).toSubmodule := by
          change (r.factorial : A) • DividedPowerAlgebra.dp A n (1 : A) ∈ S
          rw [Algebra.smul_def, map_natCast]
          exact hm
        exact ((S).toSubmodule.smul_mem_iff_of_isUnit
          (rankOneDPPrimeBlock_factorial_isUnit hprime hp hr)).mp hs

/-- 概要：標数 p の一元分冪代数は可算個の素数冪次数の分冪で生成される。
方針：全標準分冪の所属と、それらの係数線形生成を使う。
規約：部分代数の等式として述べる。
使われ方：BS Rem 7.15(1)（著者版 p.62）の切断多項式射の全射性。 -/
theorem dividedPowerPrime_adjoin_eq_top (hp : (p : A) = 0) : S = ⊤ := by
  have hspan : Submodule.span A (Set.range fun n : ℕ =>
      DividedPowerAlgebra.dp A n (1 : A)) ≤ (S).toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact dividedPower_dp_mem_prime_adjoin p hp n
  rw [rankOneDP_span_eq_top] at hspan
  apply top_unique
  intro x _hx
  exact hspan (Submodule.mem_top)

/-- 概要：可算個の変数の p 乗を零とする具体的多項式商。
方針：既存のモニック冪関係イデアルで全ての右辺を零にする。
規約：この定義自体には係数環の標数を要求しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の切断多項式表示の台環。 -/
abbrev DividedPowerPrimeTruncatedAlgebra :=
  MvPolynomial ℕ A ⧸ monicPowerFamilyRelationIdeal p ℕ A (fun _ => 0)

/-- 概要：各切断変数を対応する γₚⁿ へ送る標準係数代数射。
方針：各 γₚⁿ の p 乗消滅により、通常多項式評価射を商へ降ろす。
規約：この段階で単射性は主張しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の具体的切断多項式表示。 -/
def dividedPowerPrimeTruncatedEval (hp : (p : A) = 0) :
    DividedPowerPrimeTruncatedAlgebra (A := A) p →ₐ[A] DA := by
  let g : MvPolynomial ℕ A →ₐ[A] DA :=
    MvPolynomial.aeval (fun n : ℕ => DividedPowerAlgebra.dp A (p ^ n) (1 : A))
  apply Ideal.Quotient.liftₐ _ g
  intro f hf
  have hker : monicPowerFamilyRelationIdeal p ℕ A (fun _ => 0) ≤ RingHom.ker g.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨n, rfl⟩
    change g (MvPolynomial.X n ^ p - MvPolynomial.C (0 : A)) = 0
    simp [g, dividedPowerPrimePower_pow_zero p hp]
  exact hker hf

/-- 概要：標準評価射は n 番目の切断変数を γₚⁿ に送る。
方針：商からの評価射と多項式評価の定義を使う。
規約：変数の番号を保持する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の生成元の照合。 -/
theorem dividedPowerPrimeTruncatedEval_X (hp : (p : A) = 0) (n : ℕ) :
    dividedPowerPrimeTruncatedEval p hp
      (Ideal.Quotient.mk _ (MvPolynomial.X n)) = DividedPowerAlgebra.dp A (p ^ n) (1 : A) := by
  simp [dividedPowerPrimeTruncatedEval]

/-- 概要：可算切断多項式商から一元分冪代数への標準評価射は全射。
方針：その像が全ての素数冪分冪生成元を含み、それらが全代数を生成することを使う。
規約：単射性は別工程であり、この結果を同型とは数えない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の切断表示の一方向。 -/
theorem dividedPowerPrimeTruncatedEval_surjective (hp : (p : A) = 0) :
    Function.Surjective (dividedPowerPrimeTruncatedEval (A := A) p hp) := by
  have hle : S ≤ (dividedPowerPrimeTruncatedEval (A := A) p hp).range := by
    apply Algebra.adjoin_le
    rintro _ ⟨n, rfl⟩
    exact ⟨Ideal.Quotient.mk _ (MvPolynomial.X n), dividedPowerPrimeTruncatedEval_X p hp n⟩
  rw [dividedPowerPrime_adjoin_eq_top p hp] at hle
  intro x
  exact hle (by trivial)

omit [Fact p.Prime] in
/-- 概要：切断多項式表示の関係イデアルは全変数の p 乗で生成される。
方針：モニック冪関係の右辺を零にした定義を展開する。
規約：この表示の等式には標数や素数性は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の具体的な gᵢᵖ=0 の商表示。 -/
theorem dividedPowerPrimeTruncated_relationIdeal :
    monicPowerFamilyRelationIdeal p ℕ A (fun _ => 0) =
      Ideal.span (Set.range fun n : ℕ => (MvPolynomial.X n : MvPolynomial ℕ A) ^ p) := by
  simp [monicPowerFamilyRelationIdeal]

omit [Fact p.Prime] in
/-- 概要：切断多項式商からの係数代数射は全変数上の値で一意に決まる。
方針：商と多項式代数の二つの射の外延性を使う。
規約：終域に標数や非零性を仮定しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の具体的表示の互換射。 -/
theorem dividedPowerPrimeTruncatedHom_ext {B : Type u} [CommRing B] [Algebra A B]
    (f g : DividedPowerPrimeTruncatedAlgebra (A := A) p →ₐ[A] B)
    (h : ∀ n : ℕ, f (Ideal.Quotient.mk _ (MvPolynomial.X n)) =
      g (Ideal.Quotient.mk _ (MvPolynomial.X n))) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro n
  exact h n

end SerrePositivity.BhattScholze.Andre
