module

public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.BhattScholze.Andre.Remark715.RegularPowerQuotientTorsion
public import SerrePositivity.CommutativeAlgebra.AdicCompletenessSup
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedTorsionComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalQuotientComplete

/-!
# André E1・E2：有界試験 prism の共通二元イデアルに沿う古典的完備性

## 概要

prism 商の p 冪ねじれが有界なら、台環は (p,d) に沿って古典的完備となり、p 進分離でもある。
BS Rem 7.15（著者版 p.62）の一般の有界試験 prism への根列持上げに用いる。

## 方針

全 d 冪商へねじれの有界性を移し、導来 p 完備性から古典的完備性を得る。
その後 d 完備性と組み合わせる。原典とは異なる有界指数の帰納計算による経路。

## 規約

試験 prism の完全性も、台環・商の p 正則性も要求しない。有界性は明示する。

## 使われ方

共通完備商による互換根列の一意持上げと、根の rank 1 性に必要な分離性を供給する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {B : Type u} [CommRing B] {p : ℕ} [Fact p.Prime]
variable (Q : OrientedPrism p B)
variable (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
  (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)

include hB in
/-- 概要：有界 prism の生成元の全冪商は p に沿って古典的完備。
方針：N*m のねじれ評価と商の導来完備性を、有界ねじれによる比較へ渡す。
規約：台環や商の p 正則性は不要で、零冪商も含む。
使われ方：BS Rem 7.15（著者版 p.62）の有界試験 prism の共通完備性。 -/
theorem boundedPrism_generator_power_quotient_prime_complete (m : ℕ) :
    IsAdicComplete (Ideal.span {(p : B)}) (B ⧸ (Ideal.span {Q.generator}) ^ m) := by
  obtain ⟨N, hN⟩ := hB
  change ∀ n : ℕ, ∀ x : B ⧸ Ideal.span {Q.generator},
    (p : B ⧸ Ideal.span {Q.generator}) ^ n * x = 0 →
      (p : B ⧸ Ideal.span {Q.generator}) ^ N * x = 0 at hN
  rw [Ideal.span_singleton_pow]
  apply (IsAdicComplete.map_algebraMap_iff
    (I := Ideal.span {(p : B)}) (S := B ⧸ Ideal.span {Q.generator ^ m})
    (M := B ⧸ Ideal.span {Q.generator ^ m})).mp
  rw [Ideal.map_span, Set.image_singleton, map_natCast]
  apply (isRingModuleComplete_iff_isAdicComplete_natCast_of_bounded_torsion
    (B ⧸ Ideal.span {Q.generator ^ m}) p ?_).mp
    (isModuleComplete_principal_quotient_natCast B p (Q.generator ^ m) Q.complete_p)
  refine ⟨N * m, fun n x hx => ?_⟩
  have hN' : ∀ n : ℕ, ∀ x : B ⧸ Ideal.span {Q.generator},
      (Ideal.Quotient.mk (Ideal.span {Q.generator}) (p : B)) ^ n * x = 0 →
        (Ideal.Quotient.mk (Ideal.span {Q.generator}) (p : B)) ^ N * x = 0 := by
    intro n x hx
    have hx' : (p : B ⧸ Ideal.span {Q.generator}) ^ n * x = 0 := by
      simpa only [map_natCast] using hx
    simpa only [map_natCast] using hN n x hx'
  simpa only [map_natCast] using
    regular_power_quotient_torsion_bound (p : B) Q.generator Q.generator_regular N hN' m n x
      (by simpa only [map_natCast] using hx)

include hB in
/-- 概要：有界 prism の台環は (p,d) に沿って古典的完備。
方針：d 完備性と全 d 冪商の p 完備性から和イデアルの完備性を得る。
規約：prism の完全性や p,d の正則列条件は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の一般有界試験 prism の共通完備商。 -/
theorem boundedPrism_pair_isAdicComplete :
    IsAdicComplete (Ideal.span {(p : B), Q.generator}) B := by
  let := Q.isAdicComplete_generator
  let : ∀ n : ℕ, IsAdicComplete (Ideal.span {(p : B)})
      (B ⧸ (Ideal.span {Q.generator}) ^ n) :=
    boundedPrism_generator_power_quotient_prime_complete Q hB
  have he : Ideal.span {Q.generator} ⊔ Ideal.span {(p : B)} =
      Ideal.span {(p : B), Q.generator} := by
    rw [← Ideal.span_union, Set.singleton_union]
    exact Ideal.span_pair_comm
  rw [← he]
  exact isAdicComplete_sup_of_complete_quotients (Ideal.span {Q.generator}) (Ideal.span {(p : B)})

include hB in
/-- 概要：有界 prism の商は p に沿って古典的完備。
方針：商の導来 p 完備性と定義の有界ねじれを比較定理へ供給する。
規約：試験 prism の台環にも商にも p 正則性を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の共通完備商による根列の持上げ。 -/
theorem boundedPrism_quotient_isAdicComplete_prime :
    IsAdicComplete (Ideal.span {(p : B ⧸ Q.ideal)}) (B ⧸ Q.ideal) :=
  (isRingModuleComplete_iff_isAdicComplete_natCast_of_bounded_torsion
    (B ⧸ Q.ideal) p hB).mp
    (isModuleComplete_principal_quotient_natCast B p Q.generator Q.complete_p)

include hB in
/-- 概要：有界 prism の台環は p 進分離である。
方針：(p)⊆(p,d) の冪合同を共通完備イデアルの分離性へ移す。
規約：古典的 p 完備性や p 正則性は仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の持上げた互換根列の rank 1 判定。 -/
theorem boundedPrism_isHausdorff_prime : IsHausdorff (Ideal.span {(p : B)}) B := by
  let := boundedPrism_pair_isAdicComplete Q hB
  have hle : Ideal.span {(p : B)} ≤ Ideal.span {(p : B), Q.generator} := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Ideal.subset_span (by simp)
  constructor
  intro x hx
  apply IsHausdorff.haus' (I := Ideal.span {(p : B), Q.generator})
  intro n
  exact (hx n).mono (Submodule.smul_mono_left (pow_le_pow_left' hle n))

end SerrePositivity.BhattScholze.Andre
