module

public import SerrePositivity.BhattScholze.Andre.Unconditional.VarpiPDReduction
public import SerrePositivity.BhattScholze.Andre.PrincipalDPQuotientUniversal

/-!
# André E1・E2：ϖ 還元した無限根実 pd 包の普遍性

## 概要

完全 prism 上のモニック入力について、ϖ の持上げによる無限根 pd 包の還元は、
その係数元を零にし入力元を分冪イデアルへ送る任意の標的への一意な分冪射を持つ。
BS Rem 7.15(1)（著者版 p.62）の係数還元後の pd 普遍性。

## 方針

A1-b の射影的係数商による実分冪構造と標準値の公式を使う。
原典の非零因子による帰着とは異なる射影的商の経路。
係数元の消滅から主イデアル全体を評価で殺し、商の普遍性を適用する。

## 規約

prism 商の p 正則性と正次数を要求しない。標的のねじれや完備性にも条件を課さない。

## 使われ方

係数変更後の台環の同型と組み合わせ、原典の R/ϖ 上の pd 包と比較する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
local notation "R₀" => A ⧸ Ideal.span {(p : A)}
local notation "N" => PowerRootPolynomial R₀ p (Nat.Prime.pos (Fact.out : p.Prime))
local notation "D" f => PowerRootCoefficientPDEnvelope p f
local notation "z" f => powerRootCoefficientPDInput p f

/-- 概要：ϖ の持上げで還元した実 pd 包から分冪標的への射は一意に存在する。
方針：標的の係数消滅条件を主イデアル全体へ拡張し、商の実 pd 普遍性を使う。
原典とは異なる射影的係数商からの分冪構造を使う。
規約：係数射は無限根環 N からの指定代数構造。正次数仮定は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の R/ϖ 係数上の実 pd 包の比較。 -/
theorem existsUnique_perfectPrismVarpiPDMorphism_of_unconditional
    (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic)
    {B : Type v} [CommRing B] [Algebra N B] {I : Ideal B}
    (Ht : DividedPowers I) (hzB : algebraMap N B (z f) ∈ I)
    (haB : algebraMap N B (algebraMap R₀ N
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW))) = 0) :
    ∃! F : ((D f) ⧸ Ideal.span {(algebraMap R₀ (D f)
        (Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)))}) →ₐ[N] B,
      (perfectPrismVarpiPowerRootDividedPowers_of_unconditional W hW f hf).IsDPMorphism Ht F.toRingHom := by
  let a := Ideal.Quotient.mk (Ideal.span {(p : A)}) (perfectPrismVarpiLift W hW)
  let K : Ideal (D f) := Ideal.span {algebraMap R₀ (D f) a}
  have hcoeff : principalDPEval Ht (z f) hzB (algebraMap R₀ (D f) a) = 0 := by
    rw [IsScalarTower.algebraMap_apply R₀ N (D f), AlgHom.commutes]
    exact haB
  have hK : ∀ t ∈ K, principalDPEval Ht (z f) hzB t = 0 := by
    have hle : K ≤ RingHom.ker (principalDPEval Ht (z f) hzB).toRingHom := by
      apply Ideal.span_le.mpr
      intro t ht
      have ht' : t = algebraMap R₀ (D f) a := Set.mem_singleton_iff.mp ht
      subst t
      exact hcoeff
    exact fun t ht => hle ht
  exact existsUnique_principalDPQuotientMorphism (z f) K Ht hzB hK
    (perfectPrismVarpiPowerRootDividedPowers_of_unconditional W hW f hf)
    (perfectPrismVarpiPowerRootDividedPowers_base_apply_of_unconditional W hW f hf)

end SerrePositivity.BhattScholze.Andre
