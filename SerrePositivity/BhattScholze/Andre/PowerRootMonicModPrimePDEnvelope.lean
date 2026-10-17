module

public import SerrePositivity.BhattScholze.Andre.PowerRootPolynomialDelta
public import SerrePositivity.BhattScholze.Andre.PowerRootPolynomialModPrime
public import SerrePositivity.BhattScholze.Andre.PerfectPrismMonicModPrimePDEnvelope

/-!
# André E1・E2：無限 p 冪根環上のモニック入力の実 mod p 分冪包

## 概要

p 正則・p 局所 δ 環上の無限根多項式環で、モニック入力の mod p 一次関係商に
実分冪構造と pd 普遍性を与える。完全 prism からこれらの前提を供給する。
BS Rem 7.15(1)（著者版 p.62）の無限根変数を含む実 pd 計算。

## 方針

無限根環の実 δ 構造、自由性による p 正則性、実係数商比較によるモニック入力の
mod p 正則性を既存の正則一元分冪包の構成へ渡す。

## 規約

台環は同じ無限根環の実 mod p 商上の一次関係商。
R/ϖ 係数および prismatic Frobenius 引戻しとの同定はこのファイルだけでは主張しない。

## 使われ方

原典のモニック根拡大の実 pd 包の表示を、prismatic envelope の剰余比較へ接続する。
-/

@[expose] public noncomputable section
universe u v
set_option maxRecDepth 2048
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "Q" => P ⧸ Ideal.span {(p : P)}
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(p : P)})
/-- 概要：無限根環の通常変数 Y₀ で多項式 f を評価した入力元。
方針：既存の標準評価射を名前付きの元として固定する。
規約：分冪構造の型照合で評価の内部を展開し続けないよう irreducible とする。
使われ方：BS Rem 7.15(1)（著者版 p.62）の無限根環の一元入力。 -/
@[irreducible] def powerRootMonicPDInput (f : Polynomial A) : P :=
  powerRootPolynomialBaseMap A p hp f

local notation "root" f => powerRootMonicPDInput p f

/-- 概要：名前付きモニック入力は実 mod p 商で非零因子。
方針：入力元の定義を一度だけ展開し、係数商比較で得た正則性を使う。
規約：表示の内部展開を他の分冪構造の型へ持ち込まない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の無限根 pd 包の正則入力。 -/
theorem powerRootMonicPDInput_modPrime_regular (f : Polynomial A) (hf : f.Monic) :
    IsSMulRegular Q (bar (root f)) := by
  simpa only [powerRootMonicPDInput] using
    powerRootPolynomial_monic_mod_prime_regular A p hp f hf

/-- 概要：p 局所な係数環上の無限根多項式環も p 局所。
方針：係数の単元を標準係数射で送る。
規約：係数環の p 完備性はこの段階では不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の階乗計算の入力。 -/
theorem powerRootPolynomial_primeLocal
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) :
    ∀ m : ℕ, ¬p ∣ m → IsUnit (m : P) := by
  intro m hm
  simpa only [map_natCast] using (hlocal m hm).map (algebraMap A P)

/-- 概要：無限根環上のモニック入力の実 mod p 分冪表示環の台環。
方針：通常変数 Y₀ での評価を実 mod p 商へ送って一次関係を課す。
規約：台環の定義そのものにはモニック性は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の無限根環上の pd 包。 -/
abbrev PowerRootMonicModPrimePDEnvelope (f : Polynomial A) :=
  PrincipalDPPresentation Q (bar (root f))

/-- 概要：無限根環上のモニック入力の mod p 表示環には実分冪構造がある。
方針：無限根環の δ 持ち上げと p 正則性、入力の mod p 正則性を内部で供給する。
規約：係数環の p 正則性・p 局所性・δ 構造は明示する。f の正次数は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の無限根環上の実 pd 包の構造。 -/
def powerRootMonicModPrimeDividedPowers
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (D : DeltaStructure p A) (f : Polynomial A) (hf : f.Monic) :
    DividedPowers (principalDPPositiveIdeal (bar (root f))) :=
  regularPrincipalModPrimeDividedPowers (A := P) (p := p) (powerRootPolynomial_primeLocal p hlocal)
    (powerRootPolynomial_primeRegular p hpA) (powerRootPolynomialDelta p hpA D) (root f)
    (powerRootMonicPDInput_modPrime_regular p f hf)

/-- 概要：無限根環上の入力元の n 次分冪は標準の n 次生成元。
方針：正則一元構成の生成元公式へ無限根環の実入力を代入する。
規約：全ての次数 n を含む。
使われ方：BS Rem 7.15(1)（著者版 p.62）の普遍性と明示表示の比較。 -/
theorem powerRootMonicModPrimeDividedPowers_base_apply
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (D : DeltaStructure p A) (f : Polynomial A) (hf : f.Monic) (n : ℕ) :
    (powerRootMonicModPrimeDividedPowers p hlocal hpA D f hf).dpow n
      (algebraMap Q (PowerRootMonicModPrimePDEnvelope p f) (bar (root f))) =
      principalDPGenerator (bar (root f)) n := by
  unfold powerRootMonicModPrimeDividedPowers
  with_reducible exact
    (@regularPrincipalModPrimeDividedPowers_base_apply p inferInstance P inferInstance
      (powerRootPolynomial_primeLocal p hlocal)
      (powerRootPolynomial_primeRegular p hpA) (powerRootPolynomialDelta p hpA D) (root f)
      (powerRootMonicPDInput_modPrime_regular p f hf) n)

/-- 概要：無限根環上のモニック入力の実 mod p 分冪包から分冪標的への射は一意に存在。
方針：構成した実構造と標準生成元の公式を一次関係商の普遍性へ渡す。
規約：標的の p ねじれ・正則性・δ 構造・完備性を要求しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の無限根環上の実 pd 包の普遍性。 -/
theorem existsUnique_powerRootMonicModPrimePDMorphism
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (D : DeltaStructure p A) (f : Polynomial A) (hf : f.Monic)
    {T : Type v} [CommRing T] [Algebra Q T] {I : Ideal T} (Ht : DividedPowers I)
    (hyT : algebraMap Q T (bar (root f)) ∈ I) :
    ∃! F : PowerRootMonicModPrimePDEnvelope p f →ₐ[Q] T,
      (powerRootMonicModPrimeDividedPowers p hlocal hpA D f hf).IsDPMorphism Ht F.toRingHom :=
  existsUnique_principalDPPositiveMorphism _
    (powerRootMonicModPrimeDividedPowers p hlocal hpA D f hf)
    (powerRootMonicModPrimeDividedPowers_base_apply p hlocal hpA D f hf) Ht hyT

/-- 概要：完全 prism 上の無限根環で、モニック入力の実 mod p 分冪構造を構成する。
方針：完全性から係数環の p 正則性と p 局所性を供給する。
規約：追加の正則性や分冪構造の存在を前提に残さない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の完全 prism 上の無限根 pd 包。 -/
def perfectPrismPowerRootMonicModPrimeDividedPowers
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) :
    DividedPowers (principalDPPositiveIdeal (bar (root f))) :=
  powerRootMonicModPrimeDividedPowers p (perfectPrism_primeLocal W hW) hW.p_mul_injective
    W.deltaStructure f hf

/-- 概要：完全 prism 上の無限根環のモニック入力について実 pd 普遍射は一意に存在。
方針：完全 prism から係数の全補助条件を供給した構成を適用する。
規約：モニック多項式の正次数も標的の正則性も要求しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の無限根 pd 包の具体的な普遍性。 -/
theorem existsUnique_perfectPrismPowerRootMonicModPrimePDMorphism
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic)
    {T : Type v} [CommRing T] [Algebra Q T] {I : Ideal T} (Ht : DividedPowers I)
    (hyT : algebraMap Q T (bar (root f)) ∈ I) :
    ∃! F : PowerRootMonicModPrimePDEnvelope p f →ₐ[Q] T,
      (perfectPrismPowerRootMonicModPrimeDividedPowers p W hW f hf).IsDPMorphism Ht F.toRingHom :=
  existsUnique_powerRootMonicModPrimePDMorphism p (perfectPrism_primeLocal W hW) hW.p_mul_injective
    W.deltaStructure f hf Ht hyT


/-- 概要：無限根環の実 mod p 商では p は零。
方針：定義の p 主イデアルへの所属を使う。
規約：元の係数環の標数は任意。
使われ方：BS Rem 7.15(1)（著者版 p.62）の明示切断表示への入力。 -/
theorem powerRootModPrime_prime_eq_zero : (p : Q) = 0 := by
  change bar (p : P) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

/-- 概要：無限根環上の実 mod p 分冪包の台環は入力の p 乗商上の可算切断表示。
方針：一次関係商の明示的な係数商上の代数同型を同じ実台環へ適用する。
規約：台環の同型自体にはモニック性や prism は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の無限根 pd 包の具体的な自由表示。 -/
def powerRootMonicModPrimePDEnvelope_truncatedEquiv (f : Polynomial A) :
    letI := principalDPQuotientAlgebra hp (powerRootModPrime_prime_eq_zero (A := A) p)
      (bar (root f))
    PowerRootMonicModPrimePDEnvelope p f ≃ₐ[Q ⧸ Ideal.span {(bar (root f)) ^ p}]
      PrincipalDPTruncatedPresentation p (bar (root f)) :=
  principalDPTruncatedQuotientAlgEquiv p (powerRootModPrime_prime_eq_zero p) _

/-- 概要：無限根環上の実 mod p 分冪包の台環は入力の p 乗係数商上自由。
方針：同じ既存係数商作用に明示切断表示を介した自由性を適用する。
規約：分冪構造の構成に必要なモニック性は、台加群の自由性には不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の無限根 pd 包の自由性。 -/
theorem powerRootMonicModPrimePDEnvelope_quotient_free (f : Polynomial A) :
    letI := principalDPQuotientAlgebra hp (powerRootModPrime_prime_eq_zero (A := A) p)
      (bar (root f))
    Module.Free (Q ⧸ Ideal.span {(bar (root f)) ^ p}) (PowerRootMonicModPrimePDEnvelope p f) :=
  principalDPPresentation_free_via_truncated p (powerRootModPrime_prime_eq_zero p) _

end SerrePositivity.BhattScholze.Andre
