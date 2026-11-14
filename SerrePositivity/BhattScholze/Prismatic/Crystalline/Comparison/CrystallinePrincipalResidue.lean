module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCompletedPushout
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalClassicalComparison
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCompletedPushout
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineReductionPushout
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 主完備化 H⁰ の mod p

## 概要
p 正則な可換環では、主完備化の単位は mod p で同型。

## 方針
古典的な完備化との比較の後、第一射影の核を用いる。

## 規約
mod p は指数 1 の主イデアルの商。

## 使われ方
余分な δ 座標を持つ未完備模型と完備模型の剰余の比較。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

/-- p 正則な環の主完備化の単位は、p による商で同型。 -/
theorem crystallinePrincipalCompletionUnit_isIso_modPrime (p : ℕ) (R : CommRingCat.{u})
    (hp : IsSMulRegular R (p : R)) :
    IsIso (crystallineModPrimeRingMap p (principalCompletionRingCatUnit p R)) := by
  let := principalCompletionCommRing R (p : R)
  let := principalCompletionAlgebra R (p : R)
  let C := principalCompletionRingCat p R
  let J := Ideal.span {(p : R)}
  let T := AdicCompletion J R
  let e : C ≃+* T := (principalCompletionAdicAlgEquiv R (p : R) hp).toRingEquiv
  let L : Ideal C := Ideal.span {(p : C) ^ (1 : ℕ)}
  let M : Ideal T := Ideal.span {algebraMap R T (p : R)}
  have hL : M = L.map e.toRingHom := by
    unfold L M
    rw [Ideal.map_span, Set.image_singleton, pow_one, RingEquiv.toRingHom_eq_coe,
      map_natCast, map_natCast]
  let q := (Ideal.quotientEquiv L M e hL).trans (crystallineAdicCompletionResidueEquiv (p : R))
  let E := ((modPowOneEquiv (p := p) R).trans q.symm).toCommRingCatIso
  let f := crystallineModPrimeRingMap p (principalCompletionRingCatUnit p R)
  have h : f = E.hom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply q.injective
    change q (Ideal.Quotient.mk L (principalCompletionRingCatUnit p R x)) =
      q (q.symm (Ideal.Quotient.mk J x))
    rw [RingEquiv.apply_symm_apply]
    change crystallineAdicCompletionResidueEquiv (p : R)
      (Ideal.Quotient.mk M (e (principalCompletionRingCatUnit p R x))) = _
    have hunit : e (principalCompletionRingCatUnit p R x) = algebraMap R T x :=
      principalCompletionAdicAlgEquiv_unit R (p : R) hp x
    rw [hunit]
    exact crystallineAdicCompletionResidueEquiv_mk (p : R) x
  change IsIso f
  rw [h]
  exact E.isIso_hom

end SerrePositivity.BhattScholze.Prismatic
