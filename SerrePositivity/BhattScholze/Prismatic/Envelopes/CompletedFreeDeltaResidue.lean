module

public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDeltaBounds
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletionResidue
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons

/-!
# 完備自由 δ 環の剰余

## 概要
基底生成元で割った完備自由 δ 環を、多項式環の p 完備化と比較する。

## 方針
完備化の剰余比較と係数の商を合成し、列の表示から有界ねじれを移す。

## 使われ方
変数に沿う envelope の有界性と完備平坦性。
-/

public noncomputable section

universe u

open CategoryTheory SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic

variable {A σ : Type u} [CommRing A] (d : A)

private theorem polynomial_map_quotient_ker :
    RingHom.ker (MvPolynomial.map (σ := σ) (Ideal.Quotient.mk (Ideal.span {d}))) =
      Ideal.span {MvPolynomial.C d} := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, MvPolynomial.C_dvd_iff_dvd_coeff]
  constructor
  · intro hf m
    have he := congrArg (fun g : MvPolynomial σ (A ⧸ Ideal.span {d}) => g.coeff m) hf
    rw [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero] at he
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he)
  · intro hf
    apply MvPolynomial.ext
    intro m
    rw [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (hf m))

private def polynomialQuotientEquiv :
    (MvPolynomial σ A ⧸ Ideal.span {MvPolynomial.C d}) ≃+*
      MvPolynomial σ (A ⧸ Ideal.span {d}) :=
  (Ideal.quotEquivOfEq (polynomial_map_quotient_ker (σ := σ) d).symm).trans
    (RingHom.quotientKerEquivOfSurjective (MvPolynomial.map_surjective _
      Ideal.Quotient.mk_surjective))

private theorem principalCompletion_pow_torsion {R : Type u} [CommRing R] (a : R)
    (N : ℕ) (hN : ∀ (n : ℕ) (x : R), a ^ n * x = 0 → a ^ N * x = 0)
    (n : ℕ) (x : PrincipalCompletionH0 R a) (hx : a ^ n • x = 0) :
    a ^ N • x = 0 := by
  let e := principalCompletionH0Equiv R a
  let L := principalReflectionRelation R a
  have hx' : a ^ n • e x = 0 := by rw [← e.map_smul, hx, map_zero]
  apply e.map_eq_zero_iff.mp
  rw [e.map_smul]
  obtain ⟨v, hv⟩ := (Submodule.Quotient.mk_surjective L.range) (e x)
  change principalReflectionMk R a v = e x at hv
  rw [← hv, ← map_smul] at hx'
  obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx'
  change L w = a ^ n • v at hw
  let q := Ideal.Quotient.mk (Ideal.span {a ^ n})
  have hq : q (a ^ n) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hstep (i : ℕ) : q (w i) = q a * q (w (i + 1)) := by
    apply sub_eq_zero.mp
    have h := congrArg (fun z : ℕ → R => q (z (i + 1))) hw
    simpa only [L, principalReflectionRelation, LinearMap.sub_apply, sequenceShiftRight_succ,
      LinearMap.smul_apply, LinearMap.id_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul,
      hq, zero_mul] using h
  have hshift (i k : ℕ) : q (w i) = q a ^ k * q (w (i + k)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        q (w i) = q a ^ k * q (w (i + k)) := ih
        _ = q a ^ k * (q a * q (w (i + k + 1))) := by rw [← hstep]
        _ = q a ^ (k + 1) * q (w (i + (k + 1))) := by
          rw [pow_succ, mul_assoc]
          rfl
  have hdiv (i : ℕ) : ∃ z, w i = a ^ n * z := by
    have he : q (w i) = 0 := by
      rw [hshift i n, ← map_pow, hq, zero_mul]
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he)
  choose z hz using hdiv
  have hzw : w = a ^ n • z := funext hz
  rw [hzw, map_smul] at hw
  have ht : a ^ N • v = L (a ^ N • z) := by
    rw [map_smul]
    funext i
    have he : a ^ n * (v i - L z i) = 0 := by
      rw [mul_sub, sub_eq_zero]
      exact (congrFun hw i).symm
    change a ^ N * v i = a ^ N * L z i
    exact sub_eq_zero.mp (by simpa only [mul_sub] using hN n _ he)
  rw [← hv, ← map_smul, ht]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩

/-- 完備自由 δ 環の基底生成元による商は、多項式環の p 完備化。 -/
def completedFreeDeltaResidueEquiv {p : ℕ} [Fact p.Prime] (P : OrientedPrism p A)
    (S : Type u) :
    let R := MvPolynomial (S × ℕ) (A ⧸ P.ideal)
    let := principalCompletionCommRing R (p : R)
    (completedFreeDelta P S ⧸ Ideal.span {completedFreeDeltaBase P S P.generator}) ≃+*
      PrincipalCompletionH0 R (p : R) := by
  let R := RelativeFreeDeltaRing (R := A) S
  let d : R := MvPolynomial.C P.generator
  let Q := R ⧸ Ideal.span {d}
  let B := MvPolynomial (S × ℕ) (A ⧸ P.ideal)
  let : CommRing (PDCompletionH0 R p d) := pdCompletionCommRing R p d
  let : CommRing (PrincipalCompletionH0 Q (p : Q)) := principalCompletionCommRing Q (p : Q)
  let : CommRing (PrincipalCompletionH0 B (p : B)) := principalCompletionCommRing B (p : B)
  let e : Q ≃+* B := polynomialQuotientEquiv P.generator
  exact (pdCompletionResidueEquiv R p d).trans
    (principalCompletionRingEquiv e (p : Q) (p : B) (map_natCast e p))

/-- 剰余の同型は多項式の係数を基底の剰余へ写す。 -/
theorem completedFreeDeltaResidueEquiv_unit {p : ℕ} [Fact p.Prime] (P : OrientedPrism p A)
    (S : Type u) (x : RelativeFreeDeltaRing (R := A) S) :
    let R := MvPolynomial (S × ℕ) (A ⧸ P.ideal)
    let := principalCompletionCommRing R (p : R)
    completedFreeDeltaResidueEquiv P S
        (Ideal.Quotient.mk _ (pdCompletionUnit _ p (algebraMap A _ P.generator) x)) =
      principalCompletionUnitRingHom R (p : R) (MvPolynomial.map (Ideal.Quotient.mk P.ideal) x) := by
  let R := RelativeFreeDeltaRing (R := A) S
  let d : R := MvPolynomial.C P.generator
  let Q := R ⧸ Ideal.span {d}
  let B := MvPolynomial (S × ℕ) (A ⧸ P.ideal)
  let : CommRing (PDCompletionH0 R p d) := pdCompletionCommRing R p d
  let : CommRing (PrincipalCompletionH0 Q (p : Q)) := principalCompletionCommRing Q (p : Q)
  let : CommRing (PrincipalCompletionH0 B (p : B)) := principalCompletionCommRing B (p : B)
  let e : Q ≃+* B := polynomialQuotientEquiv P.generator
  change principalCompletionRingEquiv e (p : Q) (p : B) (map_natCast e p)
      (pdCompletionResidueEquiv R p d (Ideal.Quotient.mk _ (pdCompletionUnit R p d x))) = _
  rw [pdCompletionResidueEquiv_unit, principalCompletionRingEquiv_unit]
  congr 1

/-- 完備自由 δ 環の基底生成元による商の p 冪ねじれは有界。 -/
theorem completedFreeDelta_residue_bounded {p : ℕ} [Fact p.Prime] (P : OrientedPrism p A)
    (hP : IsBoundedPrism P) (S : Type u) :
    ∃ N : ℕ, ∀ (n : ℕ)
      (x : completedFreeDelta P S ⧸ Ideal.span {completedFreeDeltaBase P S P.generator}),
      (p : _) ^ n * x = 0 → (p : _) ^ N * x = 0 := by
  let R := MvPolynomial (S × ℕ) (A ⧸ P.ideal)
  let B := PrincipalCompletionH0 R (p : R)
  let : CommRing B := principalCompletionCommRing R (p : R)
  let : Algebra R B := principalCompletionAlgebra R (p : R)
  let e := completedFreeDeltaResidueEquiv P S
  obtain ⟨N, hN⟩ := hP
  have hR (n : ℕ) (x : R) (hx : (p : R) ^ n * x = 0) : (p : R) ^ N * x = 0 := by
    apply MvPolynomial.ext
    intro m
    have hc (k : ℕ) :
        (((p : R) ^ k) * x).coeff m = (p : A ⧸ P.ideal) ^ k * x.coeff m := by
      rw [← map_natCast MvPolynomial.C, ← map_pow, MvPolynomial.coeff_C_mul]
    rw [hc, AddMonoidAlgebra.coeff_zero]
    apply hN n
    have he := congrArg (fun y : R => y.coeff m) hx
    rwa [hc, AddMonoidAlgebra.coeff_zero] at he
  refine ⟨N, fun n x hx => e.injective ?_⟩
  have h (k : ℕ) : e ((p : _) ^ k * x) = (p : R) ^ k • (e x : B) := by
    rw [map_mul, map_pow, map_natCast, Algebra.smul_def, map_pow, map_natCast]
  rw [h, map_zero]
  apply principalCompletion_pow_torsion (p : R) N hR n
  rw [← h, hx, map_zero]

end SerrePositivity.BhattScholze.Prismatic
