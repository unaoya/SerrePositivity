module

public import SerrePositivity.BhattScholze.Prism.Basic.PerfectOrientedPrism
public import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedQuotientComplete
public import SerrePositivity.CommutativeAlgebra.AdicCompletenessSup

/-!
# André E1・E2：完全 prism の共通二元イデアルに沿う古典的完備性

## 概要

完全 prism の台環は (p,d) に沿って古典的完備である。
BS Rem 7.15（著者版 p.62）の剰余根列の一意持上げに用いる完備性。

## 方針

生成元の全冪商の p 完備性を、二つのイデアルの和に沿う完備性の一般定理へ渡す。
原典とは異なる、有界ねじれによる古典的完備性と共通完備商を使う経路。

## 規約

prism 商の p 正則性や非零性は要求しない。

## 使われ方

Perfection の完備商同型に必要な、台環の共通 (p,d) 完備性を供給する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
variable {B : Type u} [CommRing B] {p : ℕ} [Fact p.Prime]
variable (Q : OrientedPrism p B) (hQ : Q.deltaStructure.IsPerfect)

include hQ in
/-- 概要：完全 prism の生成元の全冪商は元の p イデアルに沿って完備。
方針：distinguished 冪商の p 完備性を、元の係数環による作用へ戻す。
規約：零冪商・零環も含み、商の p 正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の共通二元イデアルの完備性への入力。 -/
theorem perfectPrism_generator_power_quotient_prime_complete (n : ℕ) :
    IsAdicComplete (Ideal.span {(p : B)}) (B ⧸ (Ideal.span {Q.generator}) ^ n) := by
  let := Q.isAdicComplete_p_of_perfect hQ
  rw [Ideal.span_singleton_pow]
  apply (IsAdicComplete.map_algebraMap_iff
    (I := Ideal.span {(p : B)}) (S := B ⧸ Ideal.span {Q.generator ^ n})
    (M := B ⧸ Ideal.span {Q.generator ^ n})).mp
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using
    hQ.distinguished_power_quotient_isAdicComplete (Q.isDistinguished_of_perfect hQ) n

include hQ in
/-- 概要：完全 prism の台環は (p,d) に沿って古典的完備。
方針：d 完備性と全 d 冪商の p 完備性から和イデアルの完備性を構成する。
規約：p,d が正則列であることは要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の台環と prism 商の共通完備商。 -/
theorem perfectPrism_pair_isAdicComplete :
    IsAdicComplete (Ideal.span {(p : B), Q.generator}) B := by
  let := Q.isAdicComplete_generator
  let : ∀ n : ℕ, IsAdicComplete (Ideal.span {(p : B)})
      (B ⧸ (Ideal.span {Q.generator}) ^ n) :=
    perfectPrism_generator_power_quotient_prime_complete Q hQ
  have he : Ideal.span {Q.generator} ⊔ Ideal.span {(p : B)} =
      Ideal.span {(p : B), Q.generator} := by
    rw [← Ideal.span_union, Set.singleton_union]
    exact Ideal.span_pair_comm
  rw [← he]
  exact isAdicComplete_sup_of_complete_quotients (Ideal.span {Q.generator}) (Ideal.span {(p : B)})

end SerrePositivity.BhattScholze.Andre
