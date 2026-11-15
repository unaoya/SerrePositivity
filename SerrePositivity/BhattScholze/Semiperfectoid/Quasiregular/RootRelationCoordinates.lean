module

public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootRelationBounded

/-!
# 有限根関係の座標式

## 概要
完備化に用いた列を、原典の X_i−f_i として明示する。
## 方針
多項式の単項式を根指数へ移す標準射と、完備化の単位を計算する。
## 規約
BS 著者版 Proposition 7.10。関係は第零段の根だけを殺す。
## 使われ方
drafts の有限 T の表示との比較。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.SerrePositivity.BhattScholze.Andre _root_.SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] {r : ℕ} (f : Fin r → R)

/-- 多項式変数を送ると第零段の根が得られる。 -/
theorem rootFamilyPolynomialMap_X (i : Fin r) :
    rootFamilyPolynomialMap p R (Fin r) (MvPolynomial.X i) =
      AddMonoidAlgebra.single
        (Finsupp.single i (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootVariableExponent p (Nat.Prime.pos (Fact.out : p.Prime)) 0)) 1 := by
  change AddMonoidAlgebra.mapDomain (rootFamilyNatExponent p (Fin r))
    (AddMonoidAlgebra.single (Finsupp.single i 1) 1) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  congr 1
  apply Finsupp.ext
  intro j
  classical
  by_cases h : i = j
  · subst j
    simp [rootFamilyNatExponent, _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootNatExponent, _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootVariableExponent]
  · simp [rootFamilyNatExponent, Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne (Ne.symm h),
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootNatExponent]

/-- 完備化後の関係列は、原典にある X_i−f_i である。 -/
theorem rootRelationSequence_apply (i : Fin r) :
    rootRelationSequence p R f i = rootFamilyVariable p R (Fin r) i 0 -
      algebraMap R (rootFamilyBase p R (Fin r)) (f i) := by
  change rootFamilyUnit p R (Fin r)
    (rootFamilyPolynomialMap p R (Fin r) (MvPolynomial.X i - MvPolynomial.C (f i))) = _
  rw [map_sub, map_sub, rootFamilyPolynomialMap_X, rootFamilyPolynomialMap_C]
  rfl

/-- 有限 T の通常商の単位。 -/
@[expose] def rootRelationQuotientUnit : rootFamilyBase p R (Fin r) →+* rootRelationQuotient p R f :=
  Ideal.Quotient.mk _

/-- 通常商では、第零段の根が指定された係数と一致する。 -/
theorem rootRelationQuotientUnit_variable (i : Fin r) :
    rootRelationQuotientUnit p R f (rootFamilyVariable p R (Fin r) i 0) =
      rootRelationQuotientUnit p R f (algebraMap R _ (f i)) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [rootRelationBaseIdeal_eq]
  exact Ideal.subset_span ⟨i, rootRelationSequence_apply p R f i⟩

end SerrePositivity.BhattScholze.Semiperfectoid
