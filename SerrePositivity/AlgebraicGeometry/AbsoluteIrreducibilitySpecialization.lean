module

public import SerrePositivity.AlgebraicGeometry.GenericFiniteTypePoint
public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
概要：絶対既約な多変数多項式の既約性は、稠密主開上の体への特殊化で保たれる。
方針：次数を制限した因数分解を、非定数係数の条件とともに有限型代数で表す。
規約：因子の全次数は元の多項式の全次数以下で抑える。
使われ方：滑らかなアフィン射の生成ファイバーの幾何学的既約性を広げる。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open MvPolynomial

private def BoundedMonomial (σ : Type*) (n : ℕ) := { m : σ →₀ ℕ // ∀ i, m i ≤ n }

private instance {σ : Type*} [Finite σ] (n : ℕ) : Finite (BoundedMonomial σ n) :=
  ((Set.Finite.pi' fun _ : σ => Set.finite_le_nat n).preimage
    DFunLike.coe_injective.injOn).to_subtype

private noncomputable instance {σ : Type*} [Finite σ] (n : ℕ) :
    Fintype (BoundedMonomial σ n) :=
  Fintype.ofFinite _

private def ofCoefficients {σ R : Type*} [Finite σ] [CommSemiring R] {n : ℕ}
    (c : BoundedMonomial σ n → R) : MvPolynomial σ R :=
  ∑ j, monomial j.1 (c j)

private theorem coeff_ofCoefficients {σ R : Type*} [Finite σ] [CommSemiring R] {n : ℕ}
    (c : BoundedMonomial σ n → R) (j : BoundedMonomial σ n) :
    (ofCoefficients c).coeff j.1 = c j := by
  classical
  rw [ofCoefficients, coeff_sum, Finset.sum_eq_single j]
  · simp [coeff_monomial]
  · intro i _ hij
    simp [coeff_monomial, show i.1 ≠ j.1 from fun h => hij (Subtype.ext h)]
  · simp

private theorem map_ofCoefficients {σ R S : Type*} [Finite σ]
    [CommSemiring R] [CommSemiring S] {n : ℕ} (f : R →+* S)
    (c : BoundedMonomial σ n → R) :
    map f (ofCoefficients c) = ofCoefficients (fun j => f (c j)) := by
  simp only [ofCoefficients, map_sum, map_monomial]

private theorem ofCoefficients_eq {σ R : Type*} [Finite σ] [CommSemiring R] {n : ℕ}
    (p : MvPolynomial σ R) (hp : p.totalDegree ≤ n) :
    ofCoefficients (fun j : BoundedMonomial σ n => p.coeff j.1) = p := by
  classical
  ext m
  by_cases hm : ∀ i, m i ≤ n
  · exact coeff_ofCoefficients _ ⟨m, hm⟩
  · have hc : p.coeff m = 0 := by
      by_contra h
      exact hm ((mem_restrictDegree _ _ _).mp
        (restrictTotalDegree_le_restrictDegree _ _ _ ((mem_restrictTotalDegree _ _ _).mpr hp))
        m (mem_support_iff.mpr h))
    rw [hc, ofCoefficients, coeff_sum]
    apply Finset.sum_eq_zero
    intro j _
    have hne : j.1 ≠ m := fun e => hm (e ▸ j.2)
    simp [coeff_monomial, hne]

private theorem exists_nonconstant_coeff_of_nonzero_of_not_isUnit
    {σ F : Type*} [Field F] {p : MvPolynomial σ F} (hp : p ≠ 0) (hu : ¬ IsUnit p) :
    ∃ m, m ≠ 0 ∧ p.coeff m ≠ 0 := by
  classical
  by_contra! h
  have he : p = C (p.coeff 0) := by
    ext m
    by_cases hm : m = 0
    · subst m
      simp
    · simp [coeff_C, Ne.symm hm, h m hm]
  apply hu
  rw [he]
  have hc : p.coeff 0 ≠ 0 := fun hz => hp (by rw [he, hz, map_zero])
  exact (isUnit_iff_ne_zero.mpr hc).map C

/--
概要：分数体の代数閉包上で既約な多変数多項式は、ある稠密主開上のすべての体への特殊化で既約。
方針：因子の係数と、非定数係数の線形結合を一にする補助変数を用いて方程式を立てる。
規約：体への準同型は基底の指定した非零元を零にしないものとする。
使われ方：Stacks 0557 の絶対既約な超曲面の特殊化。
-/
theorem exists_nonzero_forall_irreducible_map_of_generic
    {A K σ : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Finite σ] (P : MvPolynomial σ A)
    (hP : Irreducible (map (algebraMap A (AlgebraicClosure K)) P)) :
    ∃ a : A, a ≠ 0 ∧ ∀ (F : Type*) [Field F] (φ : A →+* F), φ a ≠ 0 →
      Irreducible (map φ P) := by
  classical
  obtain ⟨m, hm, hmP⟩ := exists_nonconstant_coeff_of_nonzero_of_not_isUnit hP.ne_zero hP.not_isUnit
  rw [coeff_map] at hmP
  let a₀ := P.coeff m
  have ha₀ : a₀ ≠ 0 := fun h => hmP (by rw [show P.coeff m = 0 from h, map_zero])
  let n := P.totalDegree
  let J := BoundedMonomial σ n
  let T := MvPolynomial (Bool × Bool × J) A
  let q (i : Bool) : MvPolynomial σ T := ofCoefficients (fun j : J => X (i, false, j))
  let u (i : Bool) : T :=
    ∑ j : J, if j.1 = 0 then 0 else X (i, true, j) * X (i, false, j)
  let E := map (algebraMap A T) P - q false * q true
  let I := Ideal.span (Set.range E.coeff ∪ Set.range (fun i => u i - 1))
  let D := T ⧸ I
  let L := AlgebraicClosure K
  have solution (v : T →ₐ[A] L)
      (hv : I ≤ RingHom.ker v.toRingHom) :
      map (algebraMap A L) P = map v.toRingHom (q false) * map v.toRingHom (q true) ∧
        ∀ i, ¬ IsUnit (map v.toRingHom (q i)) := by
    constructor
    · ext l
      have he := hv (Ideal.subset_span (Or.inl ⟨l, rfl⟩) : E.coeff l ∈ I)
      change v (E.coeff l) = 0 at he
      rw [← map_mul, coeff_map]
      change (algebraMap A L) (P.coeff l) = v ((q false * q true).coeff l)
      simpa only [E, coeff_sub, map_sub, sub_eq_zero, coeff_map, AlgHom.commutes] using he
    · intro i hi
      obtain ⟨c, _, hc⟩ := isUnit_iff_eq_C_of_isReduced.mp hi
      have hz (j : J) (hj : j.1 ≠ 0) : v (X (i, false, j)) = 0 := by
        have h := congrArg (fun p : MvPolynomial σ L => p.coeff j.1) hc
        simp only [q, map_ofCoefficients, coeff_ofCoefficients, coeff_C,
          ite_eq_right (Ne.symm hj)] at h
        exact h
      have hu := hv (Ideal.subset_span (Or.inr ⟨i, rfl⟩) : u i - 1 ∈ I)
      change v (u i - 1) = 0 at hu
      have hu' : v (u i) = 1 := by simpa only [map_sub, map_one, sub_eq_zero] using hu
      have hzero : v (u i) = 0 := by
        simp only [u, map_sum]
        apply Finset.sum_eq_zero
        intro j _
        by_cases hj : j.1 = 0 <;> simp [hj, hz]
      exact zero_ne_one (hzero.symm.trans hu')
  have noPoint : IsEmpty (D →ₐ[A] AlgebraicClosure K) := by
    refine ⟨fun f => ?_⟩
    let v := f.comp (Ideal.Quotient.mkₐ A I)
    have hv : I ≤ RingHom.ker v.toRingHom := by
      intro x hx
      change f (Ideal.Quotient.mk I x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
    obtain ⟨hEq, hUnits⟩ := solution v hv
    rcases hP.isUnit_or_isUnit hEq with h | h
    · exact hUnits false h
    · exact hUnits true h
  obtain ⟨a₁, ha₁, hKill⟩ :=
    exists_nonzero_algebraMap_eq_zero_of_isEmpty_algHom_algebraicClosure noPoint
  refine ⟨a₀ * a₁, mul_ne_zero ha₀ ha₁, ?_⟩
  intro F _ φ ha
  rw [map_mul] at ha
  have hφ₀ : φ a₀ ≠ 0 := fun h => ha (by rw [h, zero_mul])
  have hφ₁ : φ a₁ ≠ 0 := fun h => ha (by rw [h, mul_zero])
  let : Algebra A F := φ.toAlgebra
  change Irreducible (map (algebraMap A F) P)
  have hmF : (map (algebraMap A F) P).coeff m ≠ 0 := by
    rw [coeff_map]
    exact hφ₀
  have hP₀ : map (algebraMap A F) P ≠ 0 := fun e => hmF (by simp [e])
  refine ⟨fun h => ?_, fun b c hprod => ?_⟩
  · obtain ⟨d, _, hd⟩ := isUnit_iff_eq_C_of_isReduced.mp h
    exact hmF (by simp [hd, coeff_C, Ne.symm hm])
  · by_contra! hUnits
    let Q : Bool → MvPolynomial σ F := fun i => if i then c else b
    have hEq : map (algebraMap A F) P = Q false * Q true := hprod
    have hQ₀ (i : Bool) : Q i ≠ 0 := by
      cases i
      · exact fun h => hP₀ (by rw [hEq, h, zero_mul])
      · exact fun h => hP₀ (by rw [hEq, h, mul_zero])
    have hQunit (i : Bool) : ¬ IsUnit (Q i) := by
      cases i
      · exact hUnits.1
      · exact hUnits.2
    have hdeg : (Q false).totalDegree + (Q true).totalDegree ≤ n := by
      rw [← totalDegree_mul_of_isDomain (hQ₀ false) (hQ₀ true), ← hEq]
      exact Finset.sup_mono (support_map_subset (algebraMap A F) P)
    have hBound (i : Bool) : (Q i).totalDegree ≤ n := by cases i <;> omega
    choose p hp₀ hpcoeff using fun i => exists_nonconstant_coeff_of_nonzero_of_not_isUnit
      (hQ₀ i) (hQunit i)
    let j₀ (i : Bool) : J := ⟨p i, (mem_restrictDegree _ _ _).mp
      (restrictTotalDegree_le_restrictDegree _ _ _ ((mem_restrictTotalDegree _ _ _).mpr (hBound i)))
      _ (mem_support_iff.mpr (hpcoeff i))⟩
    let coordinates : Bool × Bool × J → F := fun (i, aux, j) =>
      if aux then (if j = j₀ i then ((Q i).coeff j.1)⁻¹ else 0) else (Q i).coeff j.1
    let v : T →ₐ[A] F := aeval coordinates
    have hvX (i aux : Bool) (j : J) : v (X (i, aux, j)) = coordinates (i, aux, j) :=
      aeval_X coordinates (i, aux, j)
    have hq (i : Bool) : map v.toRingHom (q i) = Q i := by
      rw [map_ofCoefficients]
      trans ofCoefficients (fun j : J => (Q i).coeff j.1)
      · congr 1
        funext j
        change v (X (i, false, j)) = _
        simp [hvX, coordinates]
      · exact ofCoefficients_eq (Q i) (hBound i)
    have hu (i : Bool) : v (u i) = 1 := by
      simp only [u, map_sum]
      rw [Finset.sum_eq_single (j₀ i)]
      · rw [ite_eq_right (hp₀ i), map_mul]
        have hne : (Q i).coeff (j₀ i).1 ≠ 0 := hpcoeff i
        simp [hvX, coordinates, hne]
      · intro j _ hj
        split_ifs
        · exact map_zero _
        · simp [hvX, coordinates, hj]
      · simp
    have hv : I ≤ RingHom.ker v.toRingHom := by
      change Ideal.span (Set.range E.coeff ∪ Set.range (fun i => u i - 1)) ≤ _
      rw [Ideal.span_le]
      rintro x (⟨l, rfl⟩ | ⟨i, rfl⟩)
      · change v (E.coeff l) = 0
        have he := congrArg (fun p : MvPolynomial σ F => p.coeff l) hEq
        rw [← hq false, ← hq true, ← map_mul, coeff_map, coeff_map] at he
        change algebraMap A F (P.coeff l) = v ((q false * q true).coeff l) at he
        simpa only [E, coeff_sub, coeff_map, map_sub, AlgHom.commutes, sub_eq_zero] using he
      · change v (u i - 1) = 0
        rw [map_sub, hu, map_one, sub_self]
    let f : D →ₐ[A] F := Ideal.Quotient.liftₐ I v fun _ hx => hv hx
    apply hφ₁
    change algebraMap A F a₁ = 0
    rw [← f.commutes, hKill, map_zero]

end SerrePositivity.AlgebraicGeometry
