module

public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionFiniteGeneratorResidue
public import Mathlib.Data.Finsupp.Weight

/-! # 全反復関係式の(p,d)係数商での最高変数除去

次数1以下と全一次係数の消滅から、最高変数分離表示の定数性を導く。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

private theorem constant_of_linear_coefficients_zero {R : Type*} [CommRing R]
    (f : MvPolynomial σ R) (hdeg : f.totalDegree ≤ 1)
    (hcoeff : ∀ s, f.coeff (Finsupp.single s 1) = 0) :
    f = MvPolynomial.C (f.coeff 0) := by
  classical
  ext m
  rw [MvPolynomial.coeff_C]
  split_ifs with hm
  · rw [← hm]
  · by_contra hc
    have hs : m ∈ f.support := MvPolynomial.mem_support_iff.mpr hc
    have hd : m.degree ≤ 1 := (MvPolynomial.le_totalDegree hs).trans hdeg
    have hpos : 0 < m.degree := Nat.pos_of_ne_zero (fun hz =>
      hm ((Finsupp.degree_eq_zero_iff m).mp hz).symm)
    have hone : m.sum (fun _ k => k) = 1 := by
      change m.degree = 1
      omega
    obtain ⟨s, rfl⟩ := (Finsupp.sum_eq_one_iff _).mp hone
    exact hc (hcoeff s)

/-- 全深さで、係数の(p,d)商に送ると新しい最高変数への依存は消える。 -/
theorem deltaDivisionFiniteGeneratorResidue_eq_C (D : DeltaStructure p A)
    (d : A) (a : σ → A) (t : σ) (n : ℕ) :
    deltaDivisionFiniteGeneratorResidue D d a t n =
      MvPolynomial.C ((deltaDivisionFiniteGeneratorResidue D d a t n).coeff 0) := by
  exact constant_of_linear_coefficients_zero _
    (deltaDivisionFiniteGeneratorResidue_degree_le_one D d a t n)
    (deltaDivisionFiniteGeneratorResidue_coefficient_zero D d a t n)

/-- 全深さの最高変数剰余多項式の全体次数は零。 -/
theorem deltaDivisionFiniteGeneratorResidue_totalDegree_zero (D : DeltaStructure p A)
    (d : A) (a : σ → A) (t : σ) (n : ℕ) :
    (deltaDivisionFiniteGeneratorResidue D d a t n).totalDegree = 0 := by
  exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mpr
    (deltaDivisionFiniteGeneratorResidue_eq_C D d a t n)

/-- 最高変数を零にした、初期有限変数だけの具体的な関係式。 -/
def deltaDivisionFiniteLowerRelation (D : DeltaStructure p A)
    (d : A) (a : σ → A) (t : σ) (n : ℕ) : MvPolynomial (σ × Fin (n + 1)) A :=
  MvPolynomial.constantCoeff
    (relativeFreeFiniteTopVariableSplitAlgEquiv n σ A
      (deltaDivisionFiniteRelationPolynomial D d a t (n + 1)))

/-- 全深さの関係式は(p,d)係数商で、最高変数を零にした初期多項式の像に一致する。 -/
theorem deltaDivisionFiniteGeneratorResidue_eq_lowerRelation (D : DeltaStructure p A)
    (d : A) (a : σ → A) (t : σ) (n : ℕ) :
    deltaDivisionFiniteGeneratorResidue D d a t n =
      MvPolynomial.C
        ((Ideal.Quotient.mk _ : RelativeFreeFiniteOldResidue (p := p) (A := A) n σ →+*
          DeltaDivisionFiniteGeneratorCoefficient (p := p) (σ := σ) d n)
          (Ideal.Quotient.mk _ (deltaDivisionFiniteLowerRelation D d a t n))) := by
  rw [deltaDivisionFiniteGeneratorResidue_eq_C]
  congr 1

end SerrePositivity.BhattScholze
