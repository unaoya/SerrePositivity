module

public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionFiniteTopDerivative
public import SerrePositivity.BhattScholze.Delta.Free.Finite.RelativeFreeFiniteDeltaTopCoefficient

/-! # 全反復除算関係式の最高変数係数と次数

通常p剰余で各深さの最高係数を基底Frobeniusの反復で表す。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
attribute [local instance] Classical.propDecidable

/-- 深さn+1の実際の関係式を最高変数分離・係数p商で表した多項式。 -/
def deltaDivisionFiniteTopResidue (D : DeltaStructure p A) (d : A) (a : σ → A) (t : σ) (n : ℕ) :
    MvPolynomial σ (RelativeFreeFiniteOldResidue (p := p) (A := A) n σ) :=
  relativeFreeFiniteTopResidueMap (p := p) n σ
    (deltaDivisionFiniteRelationPolynomial D d a t (n + 1))

/-- 基底Frobeniusの次の反復のp商像は、前の反復像のp乗。 -/
theorem deltaDivisionFiniteOldResidue_frobenius_iterate (D : DeltaStructure p A) (d : A) (n : ℕ) :
    (Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial (σ × Fin (n + 1)) A)})
      (MvPolynomial.C (D.frobeniusLift^[n] d))) ^ p =
    Ideal.Quotient.mk _ (MvPolynomial.C (D.frobeniusLift^[n + 1] d)) := by
  let q := Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial (σ × Fin (n + 1)) A)})
  let f := q.comp (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (n + 1)) A)
  have hp : q (p : MvPolynomial (σ × Fin (n + 1)) A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hp' : f (p : A) = 0 := by simpa only [f, RingHom.comp_apply, map_natCast] using hp
  change (f (D.frobeniusLift^[n] d)) ^ p = f (D.frobeniusLift^[n + 1] d)
  rw [Function.iterate_succ_apply', D.frobeniusLift_apply, map_add, map_pow, map_mul,
    hp', zero_mul, add_zero]

/-- 全深さの最高変数係数はφ^(n+1)(d)の係数像、別の生成元では零。 -/
theorem deltaDivisionFiniteTopResidue_coefficient (D : DeltaStructure p A)
    (d : A) (a : σ → A) (t : σ) (n : ℕ) (s : σ) :
    (deltaDivisionFiniteTopResidue D d a t n).coeff (Finsupp.single s 1) =
      if s = t then Ideal.Quotient.mk _ (MvPolynomial.C (D.frobeniusLift^[n + 1] d)) else 0 := by
  unfold deltaDivisionFiniteTopResidue
  rw [deltaDivisionFiniteRelationPolynomial_succ,
    relativeFreeFiniteDeltaTopCoefficient_eq_pderiv_pow]
  have hp : Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial (σ × Fin (n + 1)) A)})
      (p : MvPolynomial (σ × Fin (n + 1)) A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [deltaDivisionFiniteRelationPolynomial_top_derivative D d a t n _ hp s]
  split_ifs with h
  · exact deltaDivisionFiniteOldResidue_frobenius_iterate (σ := σ) D d n
  · rw [zero_pow (Fact.out : p.Prime).ne_zero]

/-- 自己生成元の最高変数係数の公開版。 -/
theorem deltaDivisionFiniteTopResidue_coefficient_self (D : DeltaStructure p A)
    (d : A) (a : σ → A) (t : σ) (n : ℕ) :
    (deltaDivisionFiniteTopResidue D d a t n).coeff (Finsupp.single t 1) =
      Ideal.Quotient.mk _ (MvPolynomial.C (D.frobeniusLift^[n + 1] d)) := by
  simpa using deltaDivisionFiniteTopResidue_coefficient D d a t n t

/-- 別の生成元の最高変数係数は零。 -/
theorem deltaDivisionFiniteTopResidue_coefficient_of_ne (D : DeltaStructure p A)
    (d : A) (a : σ → A) (t : σ) (n : ℕ) (s : σ) (h : s ≠ t) :
    (deltaDivisionFiniteTopResidue D d a t n).coeff (Finsupp.single s 1) = 0 := by
  simpa only [ite_eq_right h] using deltaDivisionFiniteTopResidue_coefficient D d a t n s

/-- 全反復関係式の最高変数全体に関する次数はp剰余で1以下。 -/
theorem deltaDivisionFiniteTopResidue_degree_le_one (D : DeltaStructure p A)
    (d : A) (a : σ → A) (t : σ) (n : ℕ) :
    (deltaDivisionFiniteTopResidue D d a t n).totalDegree ≤ 1 := by
  unfold deltaDivisionFiniteTopResidue
  rw [deltaDivisionFiniteRelationPolynomial_succ]
  exact relativeFreeFiniteDeltaStep_top_degree n σ D _

end SerrePositivity.BhattScholze
