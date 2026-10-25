module

public import SerrePositivity.BhattScholze.Andre.Remark715.PrincipalDPTransport
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootMonicModPrimePDEnvelope
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootMonicPDFlat

/-!
# André E1・E2：係数 mod p 無限根環上の実分冪包

## 概要

完全 prism の係数環 A の mod p 無限根環 (A/(p))[Y¹⸍ᵖ∞] 上で、
モニック入力の実分冪構造と普遍性を構成する。同じ台環は A/(p) 上自由で、
正次数入力では忠実平坦。BS Rem 7.15(1)（著者版 p.62）の係数環上の自由性の計算。

## 方針

無限根環の実 mod p 商との係数比較同型と一次関係商の移送を合成する。
同じ台環の通常の自由性・忠実平坦性には既存のモニック冪商の基底計算を使う。

## 規約

元のモニック多項式は A 上に持ち上げて与える。R/ϖ 係数への比較と
prismatic Frobenius 引戻しの同定をこのファイルだけでは主張しない。

## 使われ方

実 pd 包の構造・普遍性と通常の自由性・忠実平坦性を同じ係数環・台環へ集約する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "Q" => P ⧸ Ideal.span {(p : P)}
local notation "q" => Ideal.Quotient.mk (Ideal.span {(p : P)})
local notation "R" => A ⧸ Ideal.span {(p : A)}
local notation "bar" => Ideal.Quotient.mk (Ideal.span {(p : A)})
local notation "N" => PowerRootPolynomial R p hp
local notation "e" => powerRootPolynomialModPrimeEquiv A p hp
local notation "y" f => q (powerRootMonicPDInput p f)

/-- 概要：係数 mod p 無限根環におけるモニック多項式の指定入力元。
方針：係数を mod p に写した多項式を Y₀ で評価する。
規約：分冪構造の型照合で内部評価を展開し続けないよう irreducible とする。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数商上の実 pd 包の入力。 -/
@[irreducible] def powerRootCoefficientPDInput (f : Polynomial A) : N :=
  powerRootPolynomialBaseMap R p hp (f.map bar)

local notation "z" f => powerRootCoefficientPDInput p f

/-- 概要：実 mod p 比較同型は元の入力を係数商上の指定入力へ送る。
方針：入力元の定義を明示展開し、商同型と評価の自然性を使う。
規約：この比較自体にはモニック性は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の分冪包の係数比較。 -/
theorem powerRootCoefficientPDInput_compare (f : Polynomial A) : e (y f) = z f := by
  unfold powerRootMonicPDInput powerRootCoefficientPDInput
  rw [powerRootPolynomialModPrimeEquiv_mk, powerRootPolynomialModPrimeMap_baseMap]

/-- 概要：係数商上の無限根環の一次関係商の実台環。
方針：同じ係数商上の指定入力に γ₁=z の関係を課す。
規約：分冪構造の存在は別途構成する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の pd 包の自由性と構造の共通台環。 -/
abbrev PowerRootCoefficientPDEnvelope (f : Polynomial A) := PrincipalDPPresentation N (z f)

/-- 概要：実 mod p 無限根 pd 表示と係数商上の無限根 pd 表示は環同型。
方針：係数比較が入力を保つことを一次関係商の係数同型へ渡す。
規約：標準係数と全標準生成元を保つ同型を使う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 構造の移送。 -/
def powerRootCoefficientPDEnvelopeEquiv (f : Polynomial A) :
    PowerRootMonicModPrimePDEnvelope p f ≃+* PowerRootCoefficientPDEnvelope p f :=
  principalDPRingEquivOfEq e (y f) (z f) (powerRootCoefficientPDInput_compare p f)

/-- 概要：係数商上の無限根環の正次数イデアルに実分冪構造を与える。
方針：完全 prism 上で構成した実 mod p 構造を係数比較同型で移す。
規約：追加の分冪構造・正則性を仮定として残さない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数 mod p 無限根 pd 包。 -/
def powerRootCoefficientDividedPowers
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) : DividedPowers (principalDPPositiveIdeal (z f)) :=
  principalDPTransportDividedPowers e (y f) (z f) (powerRootCoefficientPDInput_compare p f)
    (perfectPrismPowerRootMonicModPrimeDividedPowers p W hW f hf)

/-- 概要：移送した実構造で入力元の n 次分冪は n 次標準生成元。
方針：係数同型の構造移送の公式と移送前の標準値を使う。
規約：名前付き入力を保ち、型照合では評価の内部を展開しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 普遍性への標準値。 -/
theorem powerRootCoefficientDividedPowers_base_apply
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (n : ℕ) :
    (powerRootCoefficientDividedPowers p W hW f hf).dpow n
      (algebraMap N (PowerRootCoefficientPDEnvelope p f) (z f)) = principalDPGenerator (z f) n := by
  have hsγ : ∀ k, (perfectPrismPowerRootMonicModPrimeDividedPowers p W hW f hf).dpow k
      (algebraMap Q (PowerRootMonicModPrimePDEnvelope p f) (y f)) =
        principalDPGenerator (y f) k := by
    intro k
    unfold perfectPrismPowerRootMonicModPrimeDividedPowers
    with_reducible exact
      (@powerRootMonicModPrimeDividedPowers_base_apply A inferInstance p inferInstance
        (perfectPrism_primeLocal W hW) hW.p_mul_injective W.deltaStructure f hf k)
  have h := principalDPTransportDividedPowers_base_apply e (y f) (z f)
    (powerRootCoefficientPDInput_compare p f)
    (perfectPrismPowerRootMonicModPrimeDividedPowers p W hW f hf) hsγ n
  unfold powerRootCoefficientDividedPowers
  with_reducible exact h

/-- 概要：係数商上の無限根環の実 pd 包から任意の分冪標的への射は一意に存在。
方針：移送した構造と標準値の公式を一次関係商の一般普遍性へ渡す。
規約：標的の正則性・ねじれ・δ 構造・完備性には条件を置かない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数商上の実 pd 包の普遍性。 -/
theorem existsUnique_powerRootCoefficientPDMorphism
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic)
    {T : Type v} [CommRing T] [Algebra N T] {I : Ideal T} (Ht : DividedPowers I)
    (hzT : algebraMap N T (z f) ∈ I) :
    ∃! F : PowerRootCoefficientPDEnvelope p f →ₐ[N] T,
      (powerRootCoefficientDividedPowers p W hW f hf).IsDPMorphism Ht F.toRingHom :=
  existsUnique_principalDPPositiveMorphism _ (powerRootCoefficientDividedPowers p W hW f hf)
    (powerRootCoefficientDividedPowers_base_apply p W hW f hf) Ht hzT

omit [Fact p.Prime] in
/-- 概要：係数商 A/(p) では p は零。
方針：定義の主イデアルへの所属を使う。
規約：係数環の標数は任意。
使われ方：BS Rem 7.15(1)（著者版 p.62）の通常自由性の入力。 -/
theorem powerRootCoefficient_prime_eq_zero : (p : R) = 0 := by
  change bar (p : A) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

/-- 概要：同じ実 pd 包の台環は元の係数商 A/(p) 上自由。
方針：モニック性を係数商に移し、無限根モニック冪商の既存の基底計算を使う。
規約：自由性自体に完全 prism や入力の正次数は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の基底環上の実 pd 包の自由性。 -/
theorem powerRootCoefficientPDEnvelope_free (f : Polynomial A) (hf : f.Monic) :
    Module.Free R (PowerRootCoefficientPDEnvelope p f) := by
  unfold PowerRootCoefficientPDEnvelope powerRootCoefficientPDInput
  exact powerRootMonicDPPresentation_free R p hp (Fact.out : p.Prime)
    (powerRootCoefficient_prime_eq_zero p) (f.map bar) (hf.map bar)

/-- 概要：正次数モニック入力の同じ実 pd 包の台環は A/(p) 上忠実平坦。
方針：非零係数商ではモニック次数保存と既存の忠実平坦性を使い、零係数商は自明性で扱う。
規約：正次数は元の f に要求し、係数商の非零性は仮定しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 包の基底環上の忠実平坦性。 -/
theorem powerRootCoefficientPDEnvelope_faithfullyFlat (f : Polynomial A) (hf : f.Monic)
    (hdeg : 0 < f.natDegree) : Module.FaithfullyFlat R (PowerRootCoefficientPDEnvelope p f) := by
  rcases subsingleton_or_nontrivial R with hs | hnR
  · let := hs
    let := powerRootCoefficientPDEnvelope_free p f hf
    rw [Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality]
    refine ⟨inferInstance, ?_⟩
    intro T _ _ _
    exact Module.subsingleton R T
  · let := hnR
    unfold PowerRootCoefficientPDEnvelope powerRootCoefficientPDInput
    apply powerRootMonicDPPresentation_faithfullyFlat R p hp (Fact.out : p.Prime)
      (powerRootCoefficient_prime_eq_zero p) (f.map bar) (hf.map bar)
    simpa only [hf.natDegree_map bar] using hdeg


/-- 概要：係数商上の無限根環でも p は零。
方針：係数商での等式を標準係数射で送る。
規約：非零性や完全 prism は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の明示切断表示への入力。 -/
theorem powerRootCoefficientRing_prime_eq_zero : (p : N) = 0 := by
  simpa only [map_natCast, map_zero] using
    congrArg (algebraMap R N) (powerRootCoefficient_prime_eq_zero (A := A) p)

/-- 概要：係数商上の実無限根 pd 包は入力の p 乗商上の可算切断表示を持つ。
方針：同じ一次関係商へ既存の明示切断表示同型を適用する。
規約：係数商作用は既存の principalDPQuotientAlgebra を固定する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 包の自然な係数商射の表示。 -/
def powerRootCoefficientPDEnvelope_truncatedEquiv (f : Polynomial A) :
    letI := principalDPQuotientAlgebra hp (powerRootCoefficientRing_prime_eq_zero (A := A) p)
      (z f)
    PowerRootCoefficientPDEnvelope p f ≃ₐ[N ⧸ Ideal.span {(z f) ^ p}]
      PrincipalDPTruncatedPresentation p (z f) :=
  principalDPTruncatedQuotientAlgEquiv p (powerRootCoefficientRing_prime_eq_zero p) _

end SerrePositivity.BhattScholze.Andre
