module

import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor
public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootRelationCompletion
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons

/-!
# 有限根関係の完備化と有界ねじれ

## 概要
perfectoid 係数上の有限根関係商の p 冪ねじれは有界であり、通常商は古典的にも p 完備。
## 方針
生の商の自由基底による評価を、既存の実完備化の有界ねじれ定理と比較同型へ渡す。
## 規約
BS 著者版 Proposition 7.10・Example 7.9 の 有界な関係商の入力。有界性を追加の仮定にしない。
## 使われ方
有限 T の有界な包絡の構成。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.SerrePositivity.DerivedCompletion _root_.SerrePositivity.BhattScholze.Andre _root_.SerrePositivity.BhattScholze.Andre.Transfinite _root_.CategoryTheory
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] {r : ℕ} (f : Fin r → R)

/-- 生の有限根関係商の p 冪ねじれは perfectoid 係数の場合 p で消える。 -/
theorem rootRelationRaw_bounded (hR : IsIntegralPerfectoid R p) :
    ∃ N : ℕ, ∀ (n : ℕ) (x : rootRelationRaw p R f),
      (p : rootRelationRaw p R f)^n * x = 0 → (p : rootRelationRaw p R f)^N * x = 0 :=
  ⟨1, rootRelationRaw_torsion_bound p R f 1 (fun n x hx => by
    simpa only [pow_one] using hR.p_mul_eq_zero_of_pow_mul_eq_zero R p n x hx)⟩

/-- 実 H⁰ 完備化後にも有限根関係商の p 冪ねじれは有界。 -/
theorem rootRelationRawCompleted_bounded (hR : IsIntegralPerfectoid R p) :
    ∃ N : ℕ, ∀ (n : ℕ) (x : rootRelationRawCompleted p R f),
      (p : rootRelationRawCompleted p R f)^n * x = 0 →
        (p : rootRelationRawCompleted p R f)^N * x = 0 := by
  let S := rootRelationRaw p R f
  letI := principalCompletionCommRing S (p : S)
  change ∃ N : ℕ, ∀ (n : ℕ) (x : PrincipalCompletionH0 S (p : S)),
    (p : PrincipalCompletionH0 S (p : S))^n * x = 0 →
      (p : PrincipalCompletionH0 S (p : S))^N * x = 0
  let D := PrincipalCompletionH0 S (p : S)
  obtain ⟨_, _, N, hN⟩ := completedUnit_pure_bounded_torsion S (p : S) (rootRelationRaw_bounded p R f hR)
  let e := (principalCompletedUnitH0Iso S (p : S)).toLinearEquiv
  change ((DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
    ((boundedAboveDerivedCompletionFunctor S (p : S)).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of S S))).obj) ≃ₗ[S] D at e
  have he (n : ℕ) (x : D) : (p : D)^n * x = (p : S)^n • x := by
    have h := (principalCompletionH0_isCompleteModuleReflection S (p : S)).mul_scalar_unit
      ((p : S)^n) x
    change principalCompletionUnitRingHom S (p : S) ((p : S)^n) * x = (p : S)^n • x at h
    have hnat : principalCompletionUnitRingHom S (p : S) (p : S) = (p : D) :=
      map_natCast (principalCompletionUnitRingHom S (p : S)) p
    rw [map_pow, hnat] at h
    exact h
  refine ⟨N, fun n x hx => ?_⟩
  have hx' : (p : S)^n • x = 0 := by rw [← he]; exact hx
  rw [he]
  apply e.symm.injective
  rw [map_smul, map_zero]
  apply hN n
  rw [← map_smul, hx', map_zero]

/-- 概要：完備な根付き基底の通常の有限商の p 冪ねじれは有界。
方針：生の関係商の実完備化の有界性を、単位を保つ環同型で移す。
規約：BS 著者版 Proposition 7.10。任意の perfectoid 商の有界性は主張しない。
使われ方：Example 7.9 の包絡へ渡す 関係商の有界性。 -/
theorem rootRelationQuotient_bounded (hR : IsIntegralPerfectoid R p) :
    ∃ N : ℕ, ∀ (n : ℕ) (x : rootRelationQuotient p R f),
      (p : rootRelationQuotient p R f)^n * x = 0 →
        (p : rootRelationQuotient p R f)^N * x = 0 := by
  obtain ⟨e, _⟩ := exists_rootRelationQuotient_rawCompleted_equiv p R f
  obtain ⟨N, hN⟩ := rootRelationRawCompleted_bounded p R f hR
  refine ⟨N, fun n x hx => ?_⟩
  apply e.injective
  have hx' : (p : rootRelationRawCompleted p R f)^n * e x = 0 := by
    simpa only [map_mul, map_pow, map_natCast, map_zero] using congrArg e hx
  simpa only [map_mul, map_pow, map_natCast, map_zero] using hN n (e x) hx'

/-- 通常の有限根関係商は古典的にも p 完備。 -/
theorem rootRelationQuotient_isAdicComplete (hR : IsIntegralPerfectoid R p) :
    IsAdicComplete (Ideal.span {(p : rootRelationQuotient p R f)}) (rootRelationQuotient p R f) :=
  (isRingModuleComplete_iff_isAdicComplete_natCast_of_bounded_torsion _ p
    (rootRelationQuotient_bounded p R f hR)).mp (rootRelationQuotient_complete p R f)

/-- 概要：通常商の実 H⁰ p 完備化と通常商自身の比較。
方針：証明した導来 p 完備性を実完備化の単位の同型へ渡す。
規約：BS 著者版 Proposition 7.10。drafts の rootQuotient の定義を保つ比較。
使われ方：未完備の商と原典・drafts の有限 T の一致。 -/
def rootRelationCompletedQuotientEquiv :
    CompletedRing p (rootRelationQuotient p R f) ≃+* rootRelationQuotient p R f :=
  principalCompletionEquivOfComplete _ (p : rootRelationQuotient p R f) (rootRelationQuotient_complete p R f)

end SerrePositivity.BhattScholze.Semiperfectoid
