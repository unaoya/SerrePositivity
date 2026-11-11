module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalQuotientComparison
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 実主元完備化の有限剰余

## 概要
実 H⁰ p 完備化の mod p は、元の環の mod p と単位を保って同型。
## 方針
p で消える商の導来完備性と、関係商・実完備化の比較を使う。
## 規約
有界ねじれ・p 正則性を仮定しない。
## 使われ方
BS 著者版 Proposition 7.10 の完備テンソルの忠実性。
-/

public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R] (p : ℕ)

/-- 実 p 完備化の mod p の標準比較。元の代表元を保つ。 -/
theorem exists_principalCompletion_modPrime_equiv :
    let H := principalCompletionRingCat p (CommRingCat.of R)
    let j := (principalCompletionRingCatUnit p (CommRingCat.of R)).hom
    let I : Ideal R := Ideal.span {(p : R)}
    ∃ e : (H ⧸ I.map j) ≃+* (R ⧸ I),
      ∀ x : R, e (Ideal.Quotient.mk _ (j x)) = Ideal.Quotient.mk I x := by
  let H := principalCompletionRingCat p (CommRingCat.of R)
  let j := (principalCompletionRingCatUnit p (CommRingCat.of R)).hom
  let I : Ideal R := Ideal.span {(p : R)}
  let Q := R ⧸ I
  let T := H ⧸ I.map j
  have hpQ : (p : Q) = 0 := by
    exact (map_natCast (Ideal.Quotient.mk I) p).symm.trans
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))
  have hpT : (p : T) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (I.map j)), ← map_natCast j]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_map_of_mem j (Ideal.subset_span (Set.mem_singleton _))
  have hQ : IsModuleComplete Q (p : Q) (ModuleCat.of Q Q) :=
    isModuleComplete_of_pow_smul_zero Q (p : Q) _ 1 (by intro x; simp [hpQ])
  have hT : IsModuleComplete T (p : T) (ModuleCat.of T T) :=
    isModuleComplete_of_pow_smul_zero T (p : T) _ 1 (by intro x; simp [hpT])
  obtain ⟨e, he⟩ := exists_principalCompletionQuotientEquiv_of_complete R p I hT
  let eQ := principalCompletionEquivOfComplete Q (p : Q) hQ
  refine ⟨e.trans eQ, fun x => ?_⟩
  have hx := RingHom.congr_fun he (Ideal.Quotient.mk I x)
  change e (Ideal.Quotient.mk _ (j x)) =
    (principalCompletionUnitRingHom Q (p : Q)) (Ideal.Quotient.mk I x) at hx
  change eQ (e (Ideal.Quotient.mk _ (j x))) = _
  rw [hx]
  exact RingHom.congr_fun (principalCompletionEquivOfComplete_comp_unit Q (p : Q) hQ)
    (Ideal.Quotient.mk I x)

end SerrePositivity.DerivedCompletion
