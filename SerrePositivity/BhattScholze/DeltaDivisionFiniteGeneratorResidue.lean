module

public import SerrePositivity.BhattScholze.DeltaDivisionFiniteTopCoefficient

/-! # 係数の(p,d)剰余での全反復関係式の最高係数消滅

p商の係数をさらにdで割る。係数商にδ構造は要求しない。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 初期p係数商をさらにdの標準係数像で割った環。 -/
abbrev DeltaDivisionFiniteGeneratorCoefficient (d : A) (n : ℕ) :=
  RelativeFreeFiniteOldResidue (p := p) (A := A) n σ ⧸
    Ideal.span {(Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial (σ × Fin (n + 1)) A)})
      (MvPolynomial.C d))}

/-- 深さn+1の最高変数表示を、係数の(p,d)商へ送った多項式。 -/
def deltaDivisionFiniteGeneratorResidue (D : DeltaStructure p A) (d : A)
    (a : σ → A) (t : σ) (n : ℕ) :
    MvPolynomial σ (DeltaDivisionFiniteGeneratorCoefficient (p := p) (σ := σ) d n) :=
  MvPolynomial.map (Ideal.Quotient.mk _ : RelativeFreeFiniteOldResidue (p := p) (A := A) n σ →+*
    DeltaDivisionFiniteGeneratorCoefficient (p := p) (σ := σ) d n)
    (deltaDivisionFiniteTopResidue D d a t n)

/-- この係数商では、基底Frobeniusの全反復のd像は零。 -/
theorem deltaDivisionFiniteGeneratorCoefficient_frobenius_zero (D : DeltaStructure p A)
    (d : A) (n m : ℕ) :
    (Ideal.Quotient.mk _ : RelativeFreeFiniteOldResidue (p := p) (A := A) n σ →+*
      DeltaDivisionFiniteGeneratorCoefficient (p := p) (σ := σ) d n)
      (Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial (σ × Fin (n + 1)) A)})
        (MvPolynomial.C (D.frobeniusLift^[m] d))) = 0 := by
  let q := Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial (σ × Fin (n + 1)) A)})
  let r : RelativeFreeFiniteOldResidue (p := p) (A := A) n σ →+*
      DeltaDivisionFiniteGeneratorCoefficient (p := p) (σ := σ) d n := Ideal.Quotient.mk _
  let f := r.comp (q.comp (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (n + 1)) A))
  have hp₀ : q (p : MvPolynomial (σ × Fin (n + 1)) A) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hp : f (p : A) = 0 := by
    change r (q (MvPolynomial.C (p : A))) = 0
    rw [map_natCast (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (n + 1)) A), hp₀, map_zero]
  have hd : f d = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  change f (D.frobeniusLift^[m] d) = 0
  induction m with
  | zero => exact hd
  | succ m ih =>
      rw [Function.iterate_succ_apply', D.frobeniusLift_apply, map_add, map_pow, map_mul,
        hp, ih, zero_mul, add_zero, zero_pow (Fact.out : p.Prime).ne_zero]

/-- 係数の(p,d)商で全最高変数係数は零。 -/
theorem deltaDivisionFiniteGeneratorResidue_coefficient_zero (D : DeltaStructure p A)
    (d : A) (a : σ → A) (t : σ) (n : ℕ) (s : σ) :
    (deltaDivisionFiniteGeneratorResidue D d a t n).coeff (Finsupp.single s 1) = 0 := by
  classical
  rw [deltaDivisionFiniteGeneratorResidue, MvPolynomial.coeff_map,
    deltaDivisionFiniteTopResidue_coefficient]
  split_ifs
  · exact deltaDivisionFiniteGeneratorCoefficient_frobenius_zero (σ := σ) D d n (n + 1)
  · exact map_zero _

/-- 係数のd商への写像でも最高変数次数の1以下という上界を保つ。 -/
theorem deltaDivisionFiniteGeneratorResidue_degree_le_one (D : DeltaStructure p A)
    (d : A) (a : σ → A) (t : σ) (n : ℕ) :
    (deltaDivisionFiniteGeneratorResidue D d a t n).totalDegree ≤ 1 := by
  have he : (deltaDivisionFiniteGeneratorResidue D d a t n).totalDegree ≤
      (deltaDivisionFiniteTopResidue D d a t n).totalDegree := by
    unfold deltaDivisionFiniteGeneratorResidue MvPolynomial.totalDegree
    exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)
  exact he.trans (deltaDivisionFiniteTopResidue_degree_le_one D d a t n)

end SerrePositivity.BhattScholze
