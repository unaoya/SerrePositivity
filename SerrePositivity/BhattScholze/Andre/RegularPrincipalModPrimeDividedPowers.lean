module

public import SerrePositivity.BhattScholze.Andre.FactorialModPrimeDividedPowers
public import SerrePositivity.BhattScholze.RegularPrincipalDPModP

/-!
# André E1・E2：正則一元入力の mod p 一次関係商の実分冪構造

## 概要

p 正則・p 局所 δ 環の元 y が mod p で非零因子なら、mod p 一次関係商の
正次数生成元イデアルに実際の分冪構造を構成する。
BS Rem 7.15(1)（著者版 p.62）の pd 包の明示計算の分冪構造側。

## 方針

階乗部分環の mod p 分冪構造を既存の具体的な環同型で移す。
正次数イデアルは全正次数標準分冪生成元の生成イデアルと同定する。

## 規約

δ 環からの持ち上げ、p 正則性・p 局所性・mod p 正則性を全て明示する。
任意の正標数環上で無条件の構造を宣言するものではない。

## 使われ方

既存の分冪標的への普遍射と合わせ、正則入力の実 pd 包の普遍性を得る。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 概要：一次関係商内の正次数分冪生成元で生成されるイデアル。
方針：次数 n+1 の標準生成元全体の span を取る。
規約：係数環と入力元を固定し、分冪構造の存在は定義に含めない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 包のイデアルの指定。 -/
def principalDPPositiveIdeal (y : A) : Ideal (PrincipalDPPresentation A y) :=
  Ideal.span (Set.range fun n : ℕ => principalDPGenerator y (n + 1))


omit [Fact p.Prime] in
/-- 概要：入力元 y の係数像は一次関係商の正次数生成元イデアルに属する。
方針：一次関係 γ₁=y と零番目の正次数生成元の所属を使う。
規約：この所属自体に正則性や標数は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の分冪値を入力元で評価する。 -/
theorem principalDPPositiveIdeal_base_mem (y : A) :
    algebraMap A (PrincipalDPPresentation A y) y ∈ principalDPPositiveIdeal y := by
  rw [← principalDPGenerator_one]
  exact Ideal.subset_span (Set.mem_range_self 0)

variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A => (p : A) * a))
variable (D : DeltaStructure p A) (y : A)
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
local notation "ys" => fun _ : Unit => y
local notation "S" => pDivisionFactorialSubring p ys
local notation "q" => Ideal.Quotient.mk (Ideal.span {(p : S)})
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(p : A)})
local notation "e" => regularPrincipalDPFactorialModPEquiv hlocal hpA D y hy

/-- 概要：mod p 正次数階乗イデアルの像は一次関係商の正次数生成元イデアル。
方針：既存比較同型の全階乗生成元上の値を使って span の生成集合を比較する。
規約：実商射と既存の環同型の合成を使用する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の分冪構造の移送。 -/
theorem regularPrincipalModPrime_positiveIdeal_map :
    ((pDivisionFactorialIdeal p ys).map q).map (e).toRingHom =
      principalDPPositiveIdeal (bar y) := by
  rw [Ideal.map_map, pDivisionFactorialIdeal, Ideal.map_span]
  unfold principalDPPositiveIdeal
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨⟨s, n⟩, rfl⟩, rfl⟩
    cases s
    exact ⟨n, (regularPrincipalDPFactorialModPEquiv_generator hlocal hpA D y hy (n + 1)).symm⟩
  · rintro ⟨n, rfl⟩
    refine ⟨(⟨pDivisionFactorialValue p ys () (n + 1),
      pDivisionFactorialSubring_value_mem ys () (n + 1)⟩ : S), ?_, ?_⟩
    · exact ⟨((), n), rfl⟩
    · exact regularPrincipalDPFactorialModPEquiv_generator hlocal hpA D y hy (n + 1)

/-- 概要：正則な持ち上げを持つ mod p 一次関係商の正次数イデアルには実分冪構造がある。
方針：階乗部分環の mod p 分冪構造を正次数イデアルの具体的な比較同型で移す。
規約：p 正則な δ 持ち上げと mod p 正則性を前提に残す。
使われ方：BS Rem 7.15(1)（著者版 p.62）の正則入力の実 pd 包の構成。 -/
def regularPrincipalModPrimeDividedPowers : DividedPowers (principalDPPositiveIdeal (bar y)) :=
  DividedPowers.ofRingEquiv (regularPrincipalModPrime_positiveIdeal_map hlocal hpA D y hy)
    (factorialModPrimeDividedPowers hlocal D ys)


/-- 概要：実 mod p 分冪構造による入力元の n 次分冪は標準の n 次生成元。
方針：階乗部分環の係数と生成元を保つ比較公式を使い、mod p 分冪値を移す。
規約：全ての n を含み、入力の持ち上げと正則性の仮定は明示したまま。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 包の普遍射の標準値。 -/
theorem regularPrincipalModPrimeDividedPowers_base_apply (n : ℕ) :
    (regularPrincipalModPrimeDividedPowers hlocal hpA D y hy).dpow n
      (algebraMap (A ⧸ Ideal.span {(p : A)}) _ (bar y)) = principalDPGenerator (bar y) n := by
  rw [← regularPrincipalDPFactorialModPEquiv_coeff hlocal hpA D y hy y]
  rw [regularPrincipalModPrimeDividedPowers, DividedPowers.ofRingEquiv_dpow_apply]
  rw [factorialModPrimeDividedPowers_base_apply hlocal D ys () n]
  exact regularPrincipalDPFactorialModPEquiv_generator hlocal hpA D y hy n

end SerrePositivity.BhattScholze.Andre
