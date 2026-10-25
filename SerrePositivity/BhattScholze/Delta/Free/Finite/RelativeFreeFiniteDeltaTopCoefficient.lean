module

public import SerrePositivity.BhattScholze.Delta.Free.Finite.RelativeFreeFiniteDeltaTopDegree
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # 有限δ像の最高変数係数

初期係数p商へのFrobenius射を明示し、最高変数の係数を偏微分で計算する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (N : ℕ) (σ : Type v)

/-- 初期有限環の補助Frobeniusとp商の合成。零係数商も含む。 -/
def relativeFreeFiniteOldFrobenius (D : DeltaStructure p A) :
    MvPolynomial (σ × Fin (N + 1)) A →+* RelativeFreeFiniteOldResidue (p := p) (A := A) N σ :=
  (Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial (σ × Fin (N + 1)) A)})).comp
    (polynomialRankOneDeltaStructure (σ × Fin (N + 1)) D).frobeniusLift

/-- 初期Frobeniusのp商像は標準商像のp乗。 -/
theorem relativeFreeFiniteOldFrobenius_apply (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteOldFrobenius N σ D f = (Ideal.Quotient.mk _ f) ^ p := by
  have hp := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton_self (p : MvPolynomial (σ × Fin (N + 1)) A))
  simp only [relativeFreeFiniteOldFrobenius, RingHom.comp_apply, DeltaStructure.frobeniusLift_apply,
    map_add, map_pow, map_mul, hp, zero_mul, add_zero]

/-- 最高変数分離後の有限Frobenius像は初期Frobeniusの係数像。 -/
theorem relativeFreeFiniteTopResidueMap_frobenius (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteTopResidueMap (p := p) N σ (relativeFreeFiniteFrobeniusStep N σ D f) =
      MvPolynomial.C (relativeFreeFiniteOldFrobenius N σ D f) := by
  rw [relativeFreeFiniteFrobeniusStep_map_of_prime_zero N σ D _
    (relativeFreeFiniteTopResidueMap_prime N σ), relativeFreeFiniteTopResidueMap_inclusion,
    ← map_pow, relativeFreeFiniteOldFrobenius_apply]

/-- 実際の有限δ像の外側最高変数X_sの係数。 -/
def relativeFreeFiniteDeltaTopCoefficient (D : DeltaStructure p A) (s : σ)
    (f : MvPolynomial (σ × Fin (N + 1)) A) : RelativeFreeFiniteOldResidue (p := p) (A := A) N σ :=
  (relativeFreeFiniteTopResidueMap (p := p) N σ (relativeFreeFiniteDeltaStep N σ D f)).coeff
    (Finsupp.single s 1)

/-- 補助rank 1δ像は最高変数の係数へ寄与しない。 -/
theorem relativeFreeFiniteDeltaTopCoefficient_eq_difference (D : DeltaStructure p A) (s : σ)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaTopCoefficient N σ D s f =
      (relativeFreeFiniteDeltaDifference N σ D
        (relativeFreeFiniteTopResidueMap (p := p) N σ) f).coeff (Finsupp.single s 1) := by
  classical
  let q := relativeFreeFiniteTopResidueMap (p := p) (A := A) N σ
  have he : q (relativeFreeFiniteDeltaStep N σ D f) =
      relativeFreeFiniteDeltaDifference N σ D q f + q (relativeFreeFiniteRankOneStep N σ D f) :=
    (sub_add_cancel _ _).symm
  unfold relativeFreeFiniteDeltaTopCoefficient
  rw [he, relativeFreeFiniteTopResidueMap_rankOneStep,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    MvPolynomial.coeff_C_of_ne_zero (by simp), add_zero]

/-- 最高変数の係数は加法的。 -/
theorem relativeFreeFiniteDeltaTopCoefficient_add (D : DeltaStructure p A) (s : σ)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaTopCoefficient N σ D s (f + g) =
      relativeFreeFiniteDeltaTopCoefficient N σ D s f +
        relativeFreeFiniteDeltaTopCoefficient N σ D s g := by
  rw [relativeFreeFiniteDeltaTopCoefficient_eq_difference,
    relativeFreeFiniteDeltaDifference_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    ← relativeFreeFiniteDeltaTopCoefficient_eq_difference,
    ← relativeFreeFiniteDeltaTopCoefficient_eq_difference]

/-- 最高変数係数のFrobenius係数Leibniz公式。 -/
theorem relativeFreeFiniteDeltaTopCoefficient_mul (D : DeltaStructure p A) (s : σ)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaTopCoefficient N σ D s (f * g) =
      relativeFreeFiniteOldFrobenius N σ D f * relativeFreeFiniteDeltaTopCoefficient N σ D s g +
        relativeFreeFiniteDeltaTopCoefficient N σ D s f *
          relativeFreeFiniteOldFrobenius N σ D g := by
  let q := relativeFreeFiniteTopResidueMap (p := p) (A := A) N σ
  have he := relativeFreeFiniteDeltaStep_map_mul_of_prime_zero N σ D q
    (relativeFreeFiniteTopResidueMap_prime N σ) f g
  rw [relativeFreeFiniteTopResidueMap_inclusion, relativeFreeFiniteTopResidueMap_inclusion] at he
  simp only [← map_pow (MvPolynomial.C : RelativeFreeFiniteOldResidue (p := p) (A := A) N σ →+*
    MvPolynomial σ (RelativeFreeFiniteOldResidue (p := p) (A := A) N σ))] at he
  rw [← relativeFreeFiniteOldFrobenius_apply N σ D f,
    ← relativeFreeFiniteOldFrobenius_apply N σ D g] at he
  have hcoeff := congrArg (fun z => z.coeff (Finsupp.single s 1)) he
  rw [mul_comm (q (relativeFreeFiniteDeltaStep N σ D f))
    (MvPolynomial.C (relativeFreeFiniteOldFrobenius N σ D g))] at hcoeff
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_C_mul] at hcoeff
  change relativeFreeFiniteDeltaTopCoefficient N σ D s (f * g) =
    relativeFreeFiniteOldFrobenius N σ D f * relativeFreeFiniteDeltaTopCoefficient N σ D s g +
      relativeFreeFiniteOldFrobenius N σ D g *
        relativeFreeFiniteDeltaTopCoefficient N σ D s f at hcoeff
  rw [mul_comm (relativeFreeFiniteOldFrobenius N σ D g)
    (relativeFreeFiniteDeltaTopCoefficient N σ D s f)] at hcoeff
  exact hcoeff

/-- 基底係数のδ像は外側最高変数の係数に寄与しない。 -/
@[simp] theorem relativeFreeFiniteDeltaTopCoefficient_C (D : DeltaStructure p A) (s : σ) (a : A) :
    relativeFreeFiniteDeltaTopCoefficient N σ D s (MvPolynomial.C a) = 0 := by
  rw [relativeFreeFiniteDeltaTopCoefficient_eq_difference, relativeFreeFiniteDeltaDifference_C]
  simp

/-- 各有限変数の最高係数は、最高段の対応する変数だけを検出する。 -/
theorem relativeFreeFiniteDeltaTopCoefficient_X (D : DeltaStructure p A) (s t : σ)
    (i : Fin (N + 1)) :
    relativeFreeFiniteDeltaTopCoefficient N σ D s (MvPolynomial.X (t, i)) =
      relativeFreeFiniteOldFrobenius N σ D
        (MvPolynomial.pderiv (s, Fin.last N) (MvPolynomial.X (t, i))) := by
  classical
  unfold relativeFreeFiniteDeltaTopCoefficient
  rw [relativeFreeFiniteDeltaStep_X]
  by_cases hi : i = Fin.last N
  · subst i
    change (relativeFreeFiniteTopResidueMap (p := p) N σ
      (MvPolynomial.X (t, Fin.last (N + 1)))).coeff (Finsupp.single s 1) = _
    rw [relativeFreeFiniteTopResidueMap_X_top]
    by_cases ht : t = s
    · subst t
      simp [MvPolynomial.pderiv_X, MvPolynomial.coeff_X]
    · simp [MvPolynomial.pderiv_X, MvPolynomial.coeff_X, ht,
        Finsupp.single_eq_single_iff]
  · have hn : i.val < N := by
      have hb := i.isLt
      by_contra h
      apply hi
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    let j : Fin (N + 1) := ⟨i.val + 1, by omega⟩
    have he : i.succ = j.castSucc := Fin.ext rfl
    rw [he, relativeFreeFiniteTopResidueMap_X_initial,
      MvPolynomial.coeff_C_of_ne_zero (by simp)]
    have hj : (t, i) ≠ (s, Fin.last N) := fun h => hi (congrArg Prod.snd h)
    rw [MvPolynomial.pderiv_X_of_ne hj, map_zero]

/-- 任意有限δ像の最高係数は、初期偏微分のFrobenius商像。 -/
theorem relativeFreeFiniteDeltaTopCoefficient_eq_frobenius_pderiv (D : DeltaStructure p A) (s : σ)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaTopCoefficient N σ D s f =
      relativeFreeFiniteOldFrobenius N σ D (MvPolynomial.pderiv (s, Fin.last N) f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg =>
      rw [relativeFreeFiniteDeltaTopCoefficient_add, map_add, map_add, hf, hg]
  | mul_X f z hf =>
      obtain ⟨t, i⟩ := z
      rw [relativeFreeFiniteDeltaTopCoefficient_mul, MvPolynomial.pderiv_mul, map_add,
        map_mul, map_mul, relativeFreeFiniteDeltaTopCoefficient_X, hf]
      ring

/-- 最高変数係数は、初期偏微分のp商像のp乗。零係数商も含む。 -/
theorem relativeFreeFiniteDeltaTopCoefficient_eq_pderiv_pow (D : DeltaStructure p A) (s : σ)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    (relativeFreeFiniteTopResidueMap (p := p) N σ (relativeFreeFiniteDeltaStep N σ D f)).coeff
      (Finsupp.single s 1) =
      (Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial (σ × Fin (N + 1)) A)})
        (MvPolynomial.pderiv (s, Fin.last N) f)) ^ p := by
  change relativeFreeFiniteDeltaTopCoefficient N σ D s f = _
  rw [relativeFreeFiniteDeltaTopCoefficient_eq_frobenius_pderiv,
    relativeFreeFiniteOldFrobenius_apply]

end SerrePositivity.BhattScholze
