module

public import SerrePositivity.BhattScholze.Andre.PrimeAdicCompletionQuotientExchange
public import SerrePositivity.BhattScholze.Andre.PowerRootPolynomialModScalar
public import SerrePositivity.BhattScholze.Andre.PowerRootEquationCompletionUniversal

/-!
# André A1-a：原典の順序による完備モニック入力環

## 概要

R⟨Y^(1/p^∞)⟩/(f) を、無限根多項式環の通常の p 完備化を f で割った環として定義する。
モニック f に対し、通常の方程式商の p 完備化と全入力元を保つ環同型を持つ。
BS Rem 7.15（著者版 p.62）の S との接続。

## 方針

全係数 p 冪商でのモニック正則性を主商と完備化の交換定理へ供給する。
原典の記述を補う、係数主商・一様なフィルトレーション比較・普遍性による経路。

## 規約

係数環の p 正則性・有界ねじれ・p 完備性は要求せず、p の正値性とモニック性を使う。
この入力環の同定から源 H の prism 性までは結論しない。

## 使われ方

原典の順序の完備入力射を、検証済みの実完備化 H の普遍性へ渡す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} [CommRing R] (p : ℕ) (hp : 0 < p) (f : Polynomial R)
local notation "P" => PowerRootPolynomial R p hp
local notation "z" => powerRootPolynomialBaseMap R p hp f
local notation "CP" => AdicCompletion (Ideal.span {(p : P)}) P
local notation "jP" => algebraMap P CP
local notation "S₀" => PowerRootEquationQuotient p hp f
local notation "CS" => AdicCompletion (Ideal.span {(p : S₀)}) S₀

/-- 概要：無限根多項式環を p 完備化してから f で割った入力環。
方針：原典の括弧の順序を通常の完備化と主商で明示する。
規約：型の定義にはモニック性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の S=R⟨Y^(1/p^∞)⟩/(f)。 -/
abbrev PowerRootMonicCompletedInput := CP ⧸ Ideal.span {jP z}

/-- 概要：モニック入力では完備化してから割る環と、割ってから完備化する環は同型。
方針：モニック入力の全 p 冪商での正則性を完備化と主商の交換に使う。
規約：元の係数環の p 正則性は仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の原典の S を既存の完備入力へ接続する。 -/
def powerRootMonicCompletedInputEquiv (hf : f.Monic) :
    PowerRootMonicCompletedInput p hp f ≃+* CS :=
  primeAdicCompletionQuotientEquiv P p z
    (fun n => powerRootPolynomial_monic_mod_prime_power_regular R p hp f hf n)

/-- 概要：完備入力環の交換同型は元の無限根多項式の全ての像を保つ。
方針：一般の主商交換同型の係数公式を使う。
規約：係数元と全段の根変数もこの式に含まれる。
使われ方：BS Rem 7.15（著者版 p.62）の試験射と根の追跡。 -/
theorem powerRootMonicCompletedInputEquiv_coeff (hf : f.Monic) (x : P) :
    powerRootMonicCompletedInputEquiv p hp f hf
      (Ideal.Quotient.mk (Ideal.span {jP z}) (jP x)) =
        algebraMap S₀ CS (Ideal.Quotient.mk (Ideal.span {z}) x) :=
  primeAdicCompletionQuotientEquiv_coeff P p z
    (fun n => powerRootPolynomial_monic_mod_prime_power_regular R p hp f hf n) x

/-- 概要：原典の順序で作ったモニック完備入力環は p 完備。
方針：全 p 冪商でのモニック正則性と完備化後の主商の完備性を使う。
規約：係数環に p 正則性・有界ねじれを追加しない。
使われ方：BS Rem 7.15（著者版 p.62）の S の通常の完備性。 -/
theorem powerRootMonicCompletedInput_isAdicComplete (hf : f.Monic) :
    IsAdicComplete (Ideal.span {(p : PowerRootMonicCompletedInput p hp f)})
      (PowerRootMonicCompletedInput p hp f) :=
  primeAdicCompletion_principal_quotient_isAdicComplete P p z
    (fun n => powerRootPolynomial_monic_mod_prime_power_regular R p hp f hf n)

end SerrePositivity.BhattScholze.Andre
