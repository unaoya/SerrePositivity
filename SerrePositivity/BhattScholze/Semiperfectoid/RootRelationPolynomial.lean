module

public import SerrePositivity.CommutativeAlgebra.KoszulRegular.MonicRelation
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Xi−fi の通常多項式環での正則性と剰余

## 概要
各変数から指定された係数を引く列は Koszul 正則で、その通常商は係数環。
## 方針
既存のモニック関係の正則性を使い、評価と係数包含で商の同型を作る。
## 規約
BS 著者版 Proposition 7.10 の有限 T。係数の正則性・非零性は不要。
## 使われ方
小数指数基底を基底変更し、有限根関係商の自由性を得る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open Andre
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R] {r : ℕ} (f : Fin r → R)

/-- 各変数から指定された係数を引く初期関係。 -/
def rootRelationPolynomial (i : Fin r) : MvPolynomial (Fin r) R :=
  MvPolynomial.X i - MvPolynomial.C (f i)

/-- 通常の初期関係の生成イデアル。 -/
def rootRelationPolynomialIdeal : Ideal (MvPolynomial (Fin r) R) :=
  Ideal.span (Set.range (rootRelationPolynomial R f))

/-- Xi−fi の有限列は、既存のモニック関係の Koszul 分解を与える。 -/
theorem rootRelationPolynomial_isKoszulResolution :
    SerrePositivity.IsKoszulResolution (rootRelationPolynomial R f) := by
  unfold rootRelationPolynomial
  have h := monicRelation_fin_isKoszulResolution
    (fun i : Fin r => Polynomial.X - Polynomial.C (f i))
    (fun i => Polynomial.monic_X_sub_C (f i)) (fun i : Fin r => i) Function.injective_id
  simpa only [monicRelation, Polynomial.eval₂_sub, Polynomial.eval₂_X,
    Polynomial.eval₂_C, rootRelationPolynomial] using h

/-- Xi を fi で評価した、通常商から係数環への代数射。 -/
def rootRelationPolynomialEvaluation :
    (MvPolynomial (Fin r) R ⧸ rootRelationPolynomialIdeal R f) →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval f) (by
    change rootRelationPolynomialIdeal R f ≤ RingHom.ker (MvPolynomial.aeval f).toRingHom
    rw [rootRelationPolynomialIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [rootRelationPolynomial])

/-- 評価は商の各変数を指定された係数へ送る。 -/
theorem rootRelationPolynomialEvaluation_X (i : Fin r) :
    rootRelationPolynomialEvaluation R f
      (Ideal.Quotient.mk _ (MvPolynomial.X i)) = f i := by
  simp [rootRelationPolynomialEvaluation]

/-- 商での各変数は指定された係数に等しい。 -/
theorem rootRelationPolynomialQuotient_X (i : Fin r) :
    Ideal.Quotient.mk (rootRelationPolynomialIdeal R f) (MvPolynomial.X i) =
      algebraMap R (MvPolynomial (Fin r) R ⧸ rootRelationPolynomialIdeal R f) (f i) := by
  apply Ideal.Quotient.eq.mpr
  exact Ideal.subset_span ⟨i, rfl⟩

/-- 概要：Xi−fi の通常多項式商は係数環と代数同型。
方針：評価と係数包含を両逆にし、変数の像で照合する。
規約：BS 著者版 Proposition 7.10。零環も含む。
使われ方：有限根関係商の係数環上の自由基底。 -/
def rootRelationPolynomialQuotientEquiv :
    (MvPolynomial (Fin r) R ⧸ rootRelationPolynomialIdeal R f) ≃ₐ[R] R := by
  let ev := rootRelationPolynomialEvaluation R f
  let incl := Algebra.ofId R (MvPolynomial (Fin r) R ⧸ rootRelationPolynomialIdeal R f)
  apply AlgEquiv.ofAlgHom ev incl
  · apply AlgHom.ext
    intro a
    exact ev.commutes a
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change algebraMap R (MvPolynomial (Fin r) R ⧸ rootRelationPolynomialIdeal R f)
      (ev (Ideal.Quotient.mk (rootRelationPolynomialIdeal R f) (MvPolynomial.X i))) =
      Ideal.Quotient.mk (rootRelationPolynomialIdeal R f) (MvPolynomial.X i)
    rw [rootRelationPolynomialEvaluation_X]
    exact (rootRelationPolynomialQuotient_X R f i).symm

end SerrePositivity.BhattScholze.Semiperfectoid
