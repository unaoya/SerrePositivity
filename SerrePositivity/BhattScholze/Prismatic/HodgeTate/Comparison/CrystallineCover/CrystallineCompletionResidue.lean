module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalQuotientComparison
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 結晶係数で使う実完備化の mod p

## 概要
実際の p 完備化を p で割った環を、元の環の mod p に標準単位を保って同定する。

## 方針
関係商と完備化の既存の比較を用い、p で零化される商の完備化単位を戻す。

## 規約
環の p 正則性・Noether 性・平坦性は要求しない。

## 使われ方
特定の Zp 係数射に沿った affine 項の、実完備テンソルの剰余を比較する。
-/

public noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DerivedCompletion
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R] (p : ℕ)

/-- 結晶係数で使う mod p の比較は、元の完備化単位から来る環同型である。 -/
theorem exists_crystallineCompletionResidueEquiv :
    let H := CompletedRing p R
    let j := (principalCompletionRingCatUnit p (CommRingCat.of R)).hom
    ∃ e : (H ⧸ Ideal.span {(p : H)}) ≃+* (R ⧸ Ideal.span {(p : R)}),
      ∀ x : R, e (Ideal.Quotient.mk _ (j x)) = Ideal.Quotient.mk _ x := by
  let H := CompletedRing p R
  let j := (principalCompletionRingCatUnit p (CommRingCat.of R)).hom
  let I : Ideal R := Ideal.span {(p : R)}
  let J : Ideal H := I.map j
  let T := H ⧸ J
  let Q := R ⧸ I
  have hJ : J = Ideal.span {(p : H)} := by
    dsimp only [J, I]
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hpT : (p : T) = 0 := by
    change Ideal.Quotient.mk J (p : H) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hJ]
    exact Ideal.mem_span_singleton_self _
  have hpQ : (p : Q) = 0 := by
    change Ideal.Quotient.mk I (p : R) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hT : IsModuleComplete T (p : T) (ModuleCat.of T T) := by
    apply isModuleComplete_of_natCast_pow_smul_zero T p 1
    intro t
    simp only [pow_one, hpT, zero_smul]
  have hQ : IsModuleComplete Q (p : Q) (ModuleCat.of Q Q) := by
    apply isModuleComplete_of_natCast_pow_smul_zero Q p 1
    intro t
    simp only [pow_one, hpQ, zero_smul]
  obtain ⟨e₀, he₀⟩ := exists_principalCompletionQuotientEquiv_of_complete R p I hT
  let e₁ := principalCompletionEquivOfComplete Q (p : Q) hQ
  let e₂ := Ideal.quotEquivOfEq hJ.symm
  refine ⟨e₂.trans (e₀.trans e₁), ?_⟩
  intro x
  change e₁ (e₀ (Ideal.Quotient.mk J (j x))) = Ideal.Quotient.mk I x
  have hx := RingHom.congr_fun he₀ (Ideal.Quotient.mk I x)
  change e₀ (Ideal.Quotient.mk J (j x)) =
    principalCompletionUnitRingHom Q (p : Q) (Ideal.Quotient.mk I x) at hx
  rw [hx]
  exact RingHom.congr_fun (principalCompletionEquivOfComplete_comp_unit Q (p : Q) hQ) _

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
