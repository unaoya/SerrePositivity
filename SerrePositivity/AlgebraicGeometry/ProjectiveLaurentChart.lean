module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFiniteness
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechGradedLocalization
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechComplex
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-!
概要：射影空間の標準開の局所化に使う Laurent 指数と多項式の写像。
方針：チャートに属する変数だけ負の指数を許し、指数加法モノイドの代数を取る。
規約：Proj の次数は全変数の整数指数の和。
使われ方：標準開の次数零成分を単項式ごとに分解する。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory
open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- 添字集合 T の変数にだけ負の指数を許す指数加法モノイド。 -/
def projectiveLaurentExponents (T : Finset ι) : AddSubmonoid (ι → ℤ) where
  carrier := {e | ∀ i ∉ T, 0 ≤ e i}
  zero_mem' := fun _ _ ↦ le_rfl
  add_mem' h₁ h₂ := fun i hi ↦ add_nonneg (h₁ i hi) (h₂ i hi)

/-- 自然数指数の単項式を Laurent 指数に入れる。 -/
def projectiveLaurentOfNatExponents (T : Finset ι) :
    (ι →₀ ℕ) →+ projectiveLaurentExponents T where
  toFun e := ⟨fun i ↦ (e i : ℤ), fun _ _ ↦ Int.natCast_nonneg _⟩
  map_zero' := rfl
  map_add' e e' := Subtype.ext (funext fun i ↦ by simp)

theorem projectiveLaurentOfNatExponents_injective (T : Finset ι) :
    Function.Injective (projectiveLaurentOfNatExponents T) := by
  intro e e' he
  apply Finsupp.ext
  intro i
  exact Int.ofNat_inj.mp (congrArg (fun x : projectiveLaurentExponents T ↦ x.val i) he)

/-- 大きい添字集合への制限で負の指数を許す変数が増える。 -/
def projectiveLaurentExponentRestriction {T U : Finset ι} (h : T ⊆ U) :
    projectiveLaurentExponents T →+ projectiveLaurentExponents U where
  toFun e := ⟨e.val, fun i hi ↦ e.property i fun hT ↦ hi (h hT)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Laurent 単項式の次数は全ての指数の和。 -/
def projectiveLaurentDegree [Fintype ι] (T : Finset ι) :
    projectiveLaurentExponents T →+ ℤ where
  toFun e := ∑ i, e.val i
  map_zero' := by simp
  map_add' e e' := Finset.sum_add_distrib

/-- 多変数多項式を、負の指数を許したチャートの単項式代数へ送る。 -/
def projectiveLaurentChartMap (R : Type*) [CommRing R] (T : Finset ι) :
    MvPolynomial ι R →ₐ[R] AddMonoidAlgebra R (projectiveLaurentExponents T) :=
  AddMonoidAlgebra.mapDomainAlgHom R R (projectiveLaurentOfNatExponents T)

theorem projectiveLaurentChartMap_injective (R : Type*) [CommRing R] (T : Finset ι) :
    Function.Injective (projectiveLaurentChartMap R T) :=
  AddMonoidAlgebra.mapDomain_injective (projectiveLaurentOfNatExponents_injective T)

/-- 局所化する変数の積の指数。 -/
def projectiveLaurentDenominatorExponent (T : Finset ι) : projectiveLaurentExponents T :=
  ⟨fun i ↦ if i ∈ T then 1 else 0, fun i hi ↦ by simp [hi]⟩

/-- 変数の積の逆単項式の指数。 -/
def projectiveLaurentInverseExponent (T : Finset ι) : projectiveLaurentExponents T :=
  ⟨fun i ↦ if i ∈ T then -1 else 0, fun i hi ↦ by simp [hi]⟩

private theorem projectiveLaurentDenominator_single_mul_inverse (R : Type*) [CommRing R]
    (T : Finset ι) :
    AddMonoidAlgebra.single (projectiveLaurentDenominatorExponent T) (1 : R) *
      AddMonoidAlgebra.single (projectiveLaurentInverseExponent T) 1 = 1 := by
  rw [AddMonoidAlgebra.single_mul_single, mul_one, AddMonoidAlgebra.one_def]
  congr 1
  apply Subtype.ext
  funext i
  change (if i ∈ T then (1 : ℤ) else 0) + (if i ∈ T then (-1 : ℤ) else 0) = 0
  by_cases hi : i ∈ T <;> simp [hi]

/-- チャート内では、局所化する変数の積の単項式は単元になる。 -/
theorem isUnit_projectiveLaurentDenominator (R : Type*) [CommRing R] (T : Finset ι) :
    IsUnit (AddMonoidAlgebra.single (projectiveLaurentDenominatorExponent T) (1 : R)) :=
  let h := projectiveLaurentDenominator_single_mul_inverse R T
  ⟨⟨_, _, h, by simpa only [mul_comm] using h⟩, rfl⟩

/-- 多項式の単項式は、自然数指数を整数指数と見なした Laurent 単項式へ移る。 -/
theorem projectiveLaurentChartMap_monomial (R : Type*) [CommRing R] (T : Finset ι)
    (e : ι →₀ ℕ) (r : R) :
    projectiveLaurentChartMap R T (MvPolynomial.monomial e r) =
      AddMonoidAlgebra.single (projectiveLaurentOfNatExponents T e) r :=
  AddMonoidAlgebra.mapDomain_single

/-- チャートの変数の積。 -/
def projectiveLaurentDenominator (R : Type*) [CommRing R] (T : Finset ι) :
    MvPolynomial ι R := ∏ i ∈ T, MvPolynomial.X i

/-- チャートの変数の積を Laurent 単項式として評価する。 -/
theorem projectiveLaurentChartMap_denominator (R : Type*) [CommRing R] (T : Finset ι) :
    projectiveLaurentChartMap R T (projectiveLaurentDenominator R T) =
      AddMonoidAlgebra.single (projectiveLaurentDenominatorExponent T) 1 := by
  simp only [projectiveLaurentDenominator, map_prod, MvPolynomial.X,
    projectiveLaurentChartMap_monomial, AddMonoidAlgebra.prod_single, Finset.prod_const_one]
  congr 1
  apply Subtype.ext
  funext i
  change ((projectiveLaurentExponents T).subtype
    (∑ j ∈ T, projectiveLaurentOfNatExponents T (Finsupp.single j (1 : ℕ)))) i =
      if i ∈ T then (1 : ℤ) else 0
  rw [map_sum, Finset.sum_apply]
  simp [projectiveLaurentOfNatExponents, Finsupp.single_apply, eq_comm]

/-- Laurent 単項式に分母の冪を掛けると、多項式の単項式になる。 -/
theorem projectiveLaurentExponents_clearDenominator [Finite ι] (T : Finset ι)
    (e : projectiveLaurentExponents T) :
    ∃ (n : ℕ) (m : ι →₀ ℕ), projectiveLaurentOfNatExponents T m =
      e + n • projectiveLaurentDenominatorExponent T := by
  obtain ⟨n, hn⟩ := exists_projectiveCech_commonMonomialDenominator T e.val e.property
  let a : ι → ℤ := fun i ↦ e.val i + (if i ∈ T then (n : ℤ) else 0)
  refine ⟨n, Finsupp.equivFunOnFinite.symm (fun i ↦ (a i).toNat), ?_⟩
  apply Subtype.ext
  funext i
  change (Int.ofNat (a i).toNat) =
    e.val i + n • (if i ∈ T then (1 : ℤ) else 0)
  calc
    Int.ofNat (a i).toNat = a i := Int.toNat_of_nonneg (show 0 ≤ a i from hn i)
    _ = _ := by by_cases hi : i ∈ T <;> simp [a, hi]

/--
概要：標準開の Laurent 単項式代数は、チャートの変数の積で多項式環を局所化したもの。
方針：各単項式の分母を消し、有限和では二つの分母を掛け合わせる。
規約：有限個の変数の多項式環。係数環に整域性は仮定しない。
使われ方：標準開の次数零局所化の基底を Laurent 単項式で与える。
-/
theorem projectiveLaurentChart_isLocalizationMap [Finite ι]
    (R : Type*) [CommRing R] (T : Finset ι) :
    (Submonoid.powers (projectiveLaurentDenominator R T)).IsLocalizationMap
      (projectiveLaurentChartMap R T).toRingHom.toMonoidHom := by
  classical
  let f := projectiveLaurentDenominator R T
  let ϕ := projectiveLaurentChartMap R T
  have hf : IsUnit (ϕ f) := by
    change IsUnit (projectiveLaurentChartMap R T (projectiveLaurentDenominator R T))
    rw [projectiveLaurentChartMap_denominator]
    exact isUnit_projectiveLaurentDenominator R T
  rw [Submonoid.isLocalizationMap_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, n, rfl⟩
    change IsUnit (ϕ (f ^ n))
    rw [map_pow]
    exact hf.pow n
  · intro z
    have hclear (p : AddMonoidAlgebra R (projectiveLaurentExponents T)) :
        ∃ (n : ℕ) (q : MvPolynomial ι R), p * (ϕ f) ^ n = ϕ q := by
      induction p using AddMonoidAlgebra.induction with
      | zero => exact ⟨0, 0, by simp⟩
      | single_add e r p _ _ ih =>
        obtain ⟨n, m, hm⟩ := projectiveLaurentExponents_clearDenominator T e
        have hmono : AddMonoidAlgebra.single e r * (ϕ f) ^ n = ϕ (MvPolynomial.monomial m r) := by
          change AddMonoidAlgebra.single e r *
            projectiveLaurentChartMap R T (projectiveLaurentDenominator R T) ^ n =
              projectiveLaurentChartMap R T (MvPolynomial.monomial m r)
          rw [projectiveLaurentChartMap_denominator, AddMonoidAlgebra.single_pow, one_pow,
            AddMonoidAlgebra.single_mul_single, mul_one, projectiveLaurentChartMap_monomial, hm]
        obtain ⟨n', q, hq⟩ := ih
        refine ⟨n + n', MvPolynomial.monomial m r * f ^ n' + q * f ^ n, ?_⟩
        rw [add_mul, map_add, map_mul, map_mul, map_pow, map_pow, ← hmono, ← hq, pow_add]
        simp only [mul_assoc, mul_left_comm, mul_comm]
    obtain ⟨n, q, hq⟩ := hclear z
    refine ⟨⟨q, ⟨f ^ n, ⟨n, rfl⟩⟩⟩, ?_⟩
    change z * ϕ (f ^ n) = ϕ q
    simpa only [map_pow] using hq
  · intro a b hab
    have he := projectiveLaurentChartMap_injective R T hab
    exact ⟨1, by simpa using he⟩

/-- 多項式環からの写像が与える、Laurent 単項式代数の多項式環代数構造。 -/
def projectiveLaurentChartAlgebra (R : Type*) [CommRing R] (T : Finset ι) :
    Algebra (MvPolynomial ι R) (AddMonoidAlgebra R (projectiveLaurentExponents T)) :=
  (projectiveLaurentChartMap R T).toRingHom.toAlgebra

/-- 多項式の局所化加群と Laurent 単項式代数の線形同型。 -/
def projectiveLaurentLocalizationLinearEquiv [Finite ι]
    (R : Type*) [CommRing R] (T : Finset ι) :
    LocalizedModule (Submonoid.powers (projectiveLaurentDenominator R T))
      (MvPolynomial ι R) ≃ₗ[R] AddMonoidAlgebra R (projectiveLaurentExponents T) := by
  let P := MvPolynomial ι R
  let L := AddMonoidAlgebra R (projectiveLaurentExponents T)
  letI : Algebra P L := projectiveLaurentChartAlgebra R T
  letI : IsScalarTower R P L := IsScalarTower.of_algebraMap_eq fun a ↦
    ((projectiveLaurentChartMap R T).commutes a).symm
  letI : IsLocalization (Submonoid.powers (projectiveLaurentDenominator R T)) L :=
    (isLocalization_iff_isLocalizationMap _ _).mpr (projectiveLaurentChart_isLocalizationMap R T)
  exact (IsLocalizedModule.iso _ (Algebra.linearMap P L)).restrictScalars R

/-- Laurent 代数へ移した斉次分数に分母を掛けると、その分子に戻る。 -/
theorem projectiveLaurentLocalizationLinearEquiv_mk_mul [Finite ι]
    (R : Type*) [CommRing R] (T : Finset ι) (m : MvPolynomial ι R) (n : ℕ) :
    projectiveLaurentLocalizationLinearEquiv R T
        (LocalizedModule.mk m (projDenominator (projectiveLaurentDenominator R T) n)) *
      (projectiveLaurentChartMap R T (projectiveLaurentDenominator R T)) ^ n =
      projectiveLaurentChartMap R T m := by
  let P := MvPolynomial ι R
  let L := AddMonoidAlgebra R (projectiveLaurentExponents T)
  letI : Algebra P L := projectiveLaurentChartAlgebra R T
  letI : IsLocalization (Submonoid.powers (projectiveLaurentDenominator R T)) L :=
    (isLocalization_iff_isLocalizationMap _ _).mpr (projectiveLaurentChart_isLocalizationMap R T)
  let s := projDenominator (projectiveLaurentDenominator R T) n
  have h := IsLocalizedModule.mk'_cancel' (Algebra.linearMap P L) m s
  change (s : P) • IsLocalizedModule.iso (Submonoid.powers (projectiveLaurentDenominator R T))
    (Algebra.linearMap P L) (LocalizedModule.mk m s) = Algebra.linearMap P L m at h
  rw [← map_pow, mul_comm]
  exact h

section Graded

variable [Fintype ι]

/-- 多項式の自然数指数の和を、整数次数として取る。 -/
def projectivePolynomialDegree : (ι →₀ ℕ) →+ ℤ where
  toFun e := ∑ i, (e i : ℤ)
  map_zero' := by simp
  map_add' e e' := by simp [Finset.sum_add_distrib]

/-- Laurent 単項式として写しても、多項式の次数は変わらない。 -/
theorem projectiveLaurentOfNatExponents_degree (T : Finset ι) (e : ι →₀ ℕ) :
    projectiveLaurentDegree T (projectiveLaurentOfNatExponents T e) =
      projectivePolynomialDegree e := rfl

/-- 変数の積の次数は変数の個数。 -/
theorem projectiveLaurentDenominatorExponent_degree (T : Finset ι) :
    projectiveLaurentDegree T (projectiveLaurentDenominatorExponent T) = (T.card : ℤ) := by
  change (∑ i, if i ∈ T then (1 : ℤ) else 0) = (T.card : ℤ)
  rw [← Finset.sum_filter]
  simp

/-- 逆単項式の次数は、変数の積の次数の反対。 -/
theorem projectiveLaurentInverseExponent_degree (T : Finset ι) :
    projectiveLaurentDegree T (projectiveLaurentInverseExponent T) = -(T.card : ℤ) := by
  change (∑ i, if i ∈ T then (-1 : ℤ) else 0) = -(T.card : ℤ)
  rw [← Finset.sum_filter]
  simp

/-- Laurent 単項式への埋め込みは次数を保存し、次数成分への所属を反映する。 -/
theorem projectiveLaurentChartMap_mem_grade_iff (R : Type*) [CommRing R] (T : Finset ι)
    (d : ℤ) (p : MvPolynomial ι R) :
    projectiveLaurentChartMap R T p ∈ AddMonoidAlgebra.gradeBy R (projectiveLaurentDegree T) d ↔
      p ∈ AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)) d := by
  classical
  let f := projectiveLaurentOfNatExponents T
  have hf : Function.Injective f := projectiveLaurentOfNatExponents_injective T
  have hc (e : ι →₀ ℕ) :
      (projectiveLaurentChartMap R T p).coeff (f e) = (AddMonoidAlgebra.coeff p) e := by
    exact Finsupp.mapDomain_apply_of_injective hf (AddMonoidAlgebra.coeff p) e
  constructor
  · intro hp e he
    apply hp (f e)
    rw [Finsupp.mem_support_iff, hc]
    exact Finsupp.mem_support_iff.mp he
  · intro hp e he
    have hr : e ∈ Set.range f := by
      by_contra hn
      have hz : (projectiveLaurentChartMap R T p).coeff e = 0 :=
        Finsupp.mapDomain_of_notMem_range (f := f) (AddMonoidAlgebra.coeff p) e hn
      exact (Finsupp.mem_support_iff.mp he) hz
    obtain ⟨x, rfl⟩ := hr
    apply hp x
    rw [Finsupp.mem_support_iff, ← hc]
    exact Finsupp.mem_support_iff.mp he

private theorem projectiveLaurentDenominator_mul_inverse (R : Type*) [CommRing R]
    (T : Finset ι) :
    projectiveLaurentChartMap R T (projectiveLaurentDenominator R T) *
      AddMonoidAlgebra.single (projectiveLaurentInverseExponent T) (1 : R) = 1 := by
  rw [projectiveLaurentChartMap_denominator]
  exact projectiveLaurentDenominator_single_mul_inverse R T

/-- 分母の次数を加えた次数の分子は、指定次数の Laurent 成分とちょうど対応する。 -/
theorem projectiveLaurentLocalizationLinearEquiv_mk_mem_grade_iff (R : Type*) [CommRing R]
    (T : Finset ι) (d : ℤ) (n : ℕ) (m : MvPolynomial ι R) :
    projectiveLaurentLocalizationLinearEquiv R T
      (LocalizedModule.mk m (projDenominator (projectiveLaurentDenominator R T) n)) ∈
        AddMonoidAlgebra.gradeBy R (projectiveLaurentDegree T) d ↔
      m ∈ AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))
        (d + n • (T.card : ℤ)) := by
  let A := AddMonoidAlgebra.gradeBy R (projectiveLaurentDegree T)
  let f := projectiveLaurentChartMap R T (projectiveLaurentDenominator R T)
  let g := AddMonoidAlgebra.single (projectiveLaurentInverseExponent T) (1 : R)
  have hf : f ∈ A (T.card : ℤ) := by
    change projectiveLaurentChartMap R T (projectiveLaurentDenominator R T) ∈ A (T.card : ℤ)
    rw [projectiveLaurentChartMap_denominator, ← projectiveLaurentDenominatorExponent_degree]
    exact AddMonoidAlgebra.single_mem_gradeBy _ _ _
  have hg : g ∈ A (-(T.card : ℤ)) := by
    rw [← projectiveLaurentInverseExponent_degree]
    exact AddMonoidAlgebra.single_mem_gradeBy _ _ _
  let z := projectiveLaurentLocalizationLinearEquiv R T
    (LocalizedModule.mk m (projDenominator (projectiveLaurentDenominator R T) n))
  have hz : z * f ^ n = projectiveLaurentChartMap R T m :=
    projectiveLaurentLocalizationLinearEquiv_mk_mul R T m n
  rw [← projectiveLaurentChartMap_mem_grade_iff, ← hz]
  constructor
  · intro h
    exact SetLike.mul_mem_graded h (SetLike.pow_mem_graded n hf)
  · intro h
    have hmul := SetLike.mul_mem_graded h (SetLike.pow_mem_graded n hg)
    have hfg : f ^ n * g ^ n = 1 := by
      rw [← mul_pow, projectiveLaurentDenominator_mul_inverse R T, one_pow]
    have hd : d + n • (T.card : ℤ) + n • -(T.card : ℤ) = d := by
      simp [nsmul_eq_mul, mul_neg]
    simpa only [mul_assoc, hfg, mul_one, hd, z] using hmul

/-- チャートで捻った局所化加群と同じ次数の Laurent 成分の線形同型。 -/
def projectiveLaurentGradedLocalizationLinearEquiv (R : Type*) [CommRing R]
    (T : Finset ι) (d : ℤ) :
    projectiveGradedAway (projectiveLaurentDenominator R T)
        (fun n ↦ AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))
          (d + n • (T.card : ℤ))) ≃ₗ[R]
      AddMonoidAlgebra.gradeBy R (projectiveLaurentDegree T) d := by
  let e := projectiveLaurentLocalizationLinearEquiv R T
  let A := AddMonoidAlgebra.gradeBy R (projectiveLaurentDegree T)
  let V := fun n : ℕ ↦ AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι))
    (d + n • (T.card : ℤ))
  let f := projectiveLaurentDenominator R T
  change projectiveGradedAway f V ≃ₗ[R] A d
  apply e.ofSubmodules
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply iSup_le
    intro n z hz
    obtain ⟨m, rfl⟩ := LinearMap.mem_range.mp hz
    change e (projectiveGradedFraction f V n m) ∈ A d
    rw [projectiveGradedFraction_apply]
    exact (projectiveLaurentLocalizationLinearEquiv_mk_mem_grade_iff R T d n m.val).mpr m.property
  · intro z hz
    obtain ⟨w, rfl⟩ := e.surjective z
    induction w using LocalizedModule.induction_on with
    | _ m s =>
      obtain ⟨n, hn⟩ := s.property
      have hs : s = projDenominator f n := Subtype.ext hn.symm
      subst s
      have hm : m ∈ V n :=
        (projectiveLaurentLocalizationLinearEquiv_mk_mem_grade_iff R T d n m).mp hz
      apply Submodule.mem_map.mpr
      refine ⟨_, (le_iSup (fun n ↦ LinearMap.range (projectiveGradedFraction f V n)) n)
        (LinearMap.mem_range_self _ ⟨m, hm⟩), ?_⟩
      change e (projectiveGradedFraction f V n ⟨m, hm⟩) = _
      rw [projectiveGradedFraction_apply]

/-- チャートで許される、指定次数の Laurent 指数。 -/
abbrev ProjectiveLaurentDegreeExponents (T : Finset ι) (d : ℤ) :=
  {e : projectiveLaurentExponents T // projectiveLaurentDegree T e = d}

/-- 指定次数の Laurent 多項式は、その次数の単項式に有限台を持つ係数の族。 -/
def projectiveLaurentGradeLinearEquiv (R : Type*) [CommRing R] (T : Finset ι) (d : ℤ) :
    AddMonoidAlgebra.gradeBy R (projectiveLaurentDegree T) d ≃ₗ[R]
      ProjectiveLaurentDegreeExponents T d →₀ R :=
  AddMonoidAlgebra.supportedEquivFinsupp (R := R) (S := R) {e | projectiveLaurentDegree T e = d}

/-- チャートの制限は Laurent 単項式の指数と次数を保つ。 -/
def projectiveLaurentDegreeExponentRestriction {T U : Finset ι} (h : T ⊆ U) (d : ℤ) :
    ProjectiveLaurentDegreeExponents T d → ProjectiveLaurentDegreeExponents U d :=
  fun e ↦ ⟨projectiveLaurentExponentRestriction h e.val, e.property⟩

section Restriction

variable (R : Type*) [CommRing R]

/-- チャートを狭めるとき、Laurent 単項式代数は指数を保って制限される。 -/
def projectiveLaurentChartRestriction {T U : Finset ι} (h : T ⊆ U) :
    AddMonoidAlgebra R (projectiveLaurentExponents T) →ₐ[R]
      AddMonoidAlgebra R (projectiveLaurentExponents U) :=
  AddMonoidAlgebra.mapDomainAlgHom R R (projectiveLaurentExponentRestriction h)

theorem projectiveLaurentChartRestriction_map {T U : Finset ι} (h : T ⊆ U)
    (m : MvPolynomial ι R) :
    projectiveLaurentChartRestriction R h (projectiveLaurentChartMap R T m) =
      projectiveLaurentChartMap R U m := by
  change ((AddMonoidAlgebra.mapDomainAlgHom R R (projectiveLaurentExponentRestriction h)).comp
    (AddMonoidAlgebra.mapDomainAlgHom R R (projectiveLaurentOfNatExponents T))) m = _
  rw [← AddMonoidAlgebra.mapDomainAlgHom_comp]
  rfl

/-- 追加で反転する変数の積を掛けると、狭いチャートの分母になる。 -/
theorem projectiveLaurentDenominator_sdiff {T U : Finset ι} (h : T ⊆ U) :
    projectiveLaurentDenominator R T * projectiveLaurentDenominator R (U \ T) =
      projectiveLaurentDenominator R U := by
  simp only [projectiveLaurentDenominator]
  rw [← Finset.prod_union (Finset.disjoint_sdiff : Disjoint T (U \ T))]
  congr 1
  ext i
  by_cases hi : i ∈ T
  · simp [hi, h hi]
  · simp [hi]

/-- 分母を広げてから Laurent 単項式に移す写像は、チャートの制限と可換。 -/
theorem projectiveLaurentLocalizationLinearEquiv_restriction_mk {T U : Finset ι} (h : T ⊆ U)
    (m : MvPolynomial ι R) (n : ℕ) :
    projectiveLaurentChartRestriction R h
        (projectiveLaurentLocalizationLinearEquiv R T
          (LocalizedModule.mk m (projDenominator (projectiveLaurentDenominator R T) n))) =
      projectiveLaurentLocalizationLinearEquiv R U
        (LocalizedModule.mk (projectiveLaurentDenominator R (U \ T) ^ n * m)
          (projDenominator (projectiveLaurentDenominator R U) n)) := by
  let f := projectiveLaurentDenominator R T
  let l := projectiveLaurentChartRestriction R h
  let φ := projectiveLaurentChartMap R U
  have hunit : IsUnit (φ (projectiveLaurentDenominator R U) ^ n) := by
    change IsUnit (projectiveLaurentChartMap R U (projectiveLaurentDenominator R U) ^ n)
    rw [projectiveLaurentChartMap_denominator]
    exact (isUnit_projectiveLaurentDenominator R U).pow n
  apply hunit.mul_left_inj.mp
  rw [projectiveLaurentLocalizationLinearEquiv_mk_mul,
    ← projectiveLaurentDenominator_sdiff R h, map_mul, mul_pow, ← mul_assoc]
  have hm := congrArg l (projectiveLaurentLocalizationLinearEquiv_mk_mul R T m n)
  simp only [l, map_mul, map_pow, projectiveLaurentChartRestriction_map] at hm
  rw [hm]
  simp [φ, mul_comm]

end Restriction

/-- 指定次数の Laurent 単項式による、標準開の有限交叉の加群図式。 -/
abbrev projectiveLaurentGradedChartDiagram (R : Type*) [CommRing R] (d : ℤ) :
    Finset ι ⥤ ModuleCat R where
  obj T := ModuleCat.of R (ProjectiveLaurentDegreeExponents T d →₀ R)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain R R
    (projectiveLaurentDegreeExponentRestriction (leOfHom f) d))
  map_id _ := by
    apply ModuleCat.hom_ext
    exact Finsupp.lmapDomain_id _ _
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact Finsupp.lmapDomain_comp _ _
      (projectiveLaurentDegreeExponentRestriction (leOfHom f) d)
      (projectiveLaurentDegreeExponentRestriction (leOfHom g) d)

/-- 指数が負になる変数の有限集合。 -/
def projectiveLaurentNegativeSupport (e : ι → ℤ) : Finset ι :=
  Finset.univ.filter fun i ↦ e i < 0

/-- チャートに単項式が現れる条件は、負の指数の台が添字集合に含まれること。 -/
theorem projectiveLaurentExponents_iff_negativeSupport_subset (T : Finset ι) (e : ι → ℤ) :
    e ∈ projectiveLaurentExponents T ↔ projectiveLaurentNegativeSupport e ⊆ T := by
  change (∀ i ∉ T, 0 ≤ e i) ↔ projectiveLaurentNegativeSupport e ⊆ T
  constructor
  · intro h i hi
    by_contra hn
    exact (not_lt_of_ge (h i hn)) (Finset.mem_filter.mp hi).2
  · intro h i hi
    exact le_of_not_gt fun he ↦ hi (h (Finset.mem_filter.mpr ⟨Finset.mem_univ i, he⟩))

/-- 指定次数の整数指数ベクトル。 -/
abbrev ProjectiveLaurentGlobalExponents (d : ℤ) := {e : ι → ℤ // (∑ i, e i) = d}

/-- チャートに現れる指定次数の指数を、全体の整数指数に入れる。 -/
def projectiveLaurentDegreeExponentEmbedding (T : Finset ι) (d : ℤ) :
    ProjectiveLaurentDegreeExponents T d ↪ ProjectiveLaurentGlobalExponents (ι := ι) d where
  toFun e := ⟨e.val.val, e.property⟩
  inj' := fun _ _ h ↦ Subtype.ext (Subtype.ext
    (congrArg (fun x : ProjectiveLaurentGlobalExponents (ι := ι) d ↦ x.val) h))

/-- 台の条件を満たす全体の指数を、チャート上の指数と見なす。 -/
def projectiveLaurentLiftExponent {d : ℤ} (T : Finset ι)
    (e : ProjectiveLaurentGlobalExponents (ι := ι) d)
    (h : projectiveLaurentNegativeSupport e.val ⊆ T) :
    ProjectiveLaurentDegreeExponents T d :=
  ⟨⟨e.val, (projectiveLaurentExponents_iff_negativeSupport_subset T _).mpr h⟩, e.property⟩

/-- チャートの指数の制限は単射。 -/
theorem projectiveLaurentDegreeExponentRestriction_injective {T U : Finset ι}
    (h : T ⊆ U) (d : ℤ) : Function.Injective (projectiveLaurentDegreeExponentRestriction h d) := by
  intro e e' he
  exact Subtype.ext (Subtype.ext (congrArg (fun x : ProjectiveLaurentDegreeExponents U d ↦
    x.val.val) he))

/-- 制限後に追加で現れる指数の係数は零。 -/
theorem projectiveLaurentRestriction_coeff {T U : Finset ι} (h : T ⊆ U)
    (R : Type*) [CommRing R] (d : ℤ) (a : ProjectiveLaurentDegreeExponents T d →₀ R)
    (e : ProjectiveLaurentGlobalExponents (ι := ι) d)
    (heU : projectiveLaurentNegativeSupport e.val ⊆ U) :
    (Finsupp.mapDomain (projectiveLaurentDegreeExponentRestriction h d) a)
        (projectiveLaurentLiftExponent U e heU) =
      if heT : projectiveLaurentNegativeSupport e.val ⊆ T then
        a (projectiveLaurentLiftExponent T e heT)
      else 0 := by
  classical
  split_ifs with heT
  · exact Finsupp.mapDomain_apply_of_injective
      (projectiveLaurentDegreeExponentRestriction_injective h d) a
      (projectiveLaurentLiftExponent T e heT)
  · apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨x, hx⟩
    apply heT
    have ex : x.val.val = e.val :=
      congrArg (fun x : ProjectiveLaurentDegreeExponents U d ↦ x.val.val) hx
    exact (projectiveLaurentExponents_iff_negativeSupport_subset T _).mp (ex ▸ x.val.property)

/-- 各タプルの標準開に、指定次数の Laurent 係数を置いたコチェイン。 -/
abbrev ProjectiveLaurentCochains (R : Type*) [CommRing R] (d : ℤ) (k : ℕ) :=
  FullCechCochains (projectiveLaurentGradedChartDiagram (ι := ι) R d) k

/-- 指定した単項式の係数を全タプル Čech コチェインから取り出す。 -/
def projectiveLaurentCechCoordinate (R : Type*) [CommRing R] (d : ℤ)
    (e : ProjectiveLaurentGlobalExponents (ι := ι) d) (k : ℕ) :
    ProjectiveLaurentCochains (ι := ι) R d k →ₗ[R]
      projectiveMonomialCochains (R := R) (projectiveLaurentNegativeSupport e.val) k := by
  classical
  let C := ProjectiveLaurentCochains (ι := ι) R d k
  let N := projectiveLaurentNegativeSupport e.val
  let coord : C →ₗ[R] (Fin k → ι) → R := LinearMap.pi fun t ↦
    if h : N ⊆ cechTupleSupport t then
      (Finsupp.lapply (projectiveLaurentLiftExponent (cechTupleSupport t) e h)).comp
        (LinearMap.proj t)
    else 0
  apply LinearMap.codRestrict _ coord
  intro a t ht
  simp [coord, N, ht]

/-- 単項式コチェインを Laurent 単項式を基底とする Čech コチェインに入れる。 -/
def projectiveLaurentCechSingle (R : Type*) [CommRing R] (d : ℤ)
    (e : ProjectiveLaurentGlobalExponents (ι := ι) d) (k : ℕ) :
    projectiveMonomialCochains (R := R) (projectiveLaurentNegativeSupport e.val) k →ₗ[R]
      ProjectiveLaurentCochains (ι := ι) R d k := by
  classical
  apply LinearMap.pi
  intro t
  if h : projectiveLaurentNegativeSupport e.val ⊆ cechTupleSupport t then
    let exponent := projectiveLaurentLiftExponent (cechTupleSupport t) e h
    exact (Finsupp.lsingle exponent).comp ((LinearMap.proj t).comp
      (projectiveMonomialCochains (R := R) (projectiveLaurentNegativeSupport e.val) k).subtype)
  else
    exact 0

/-- 単項式が現れる標準開では、その係数を座標として取り出す。 -/
theorem projectiveLaurentCechCoordinate_apply {R : Type*} [CommRing R] {d : ℤ}
    (e : ProjectiveLaurentGlobalExponents (ι := ι) d) (k : ℕ)
    (a : ProjectiveLaurentCochains (ι := ι) R d k) (t : Fin k → ι)
    (ht : projectiveLaurentNegativeSupport e.val ⊆ cechTupleSupport t) :
    (projectiveLaurentCechCoordinate R d e k a).val t =
      a t (projectiveLaurentLiftExponent (cechTupleSupport t) e ht) := by
  unfold projectiveLaurentCechCoordinate
  change ((if h : projectiveLaurentNegativeSupport e.val ⊆ cechTupleSupport t then
      (Finsupp.lapply (projectiveLaurentLiftExponent (cechTupleSupport t) e h)).comp
        (LinearMap.proj t)
      else 0) : ProjectiveLaurentCochains (ι := ι) R d k →ₗ[R] R) a = _
  rw [dite_eq_left ht, LinearMap.comp_apply, LinearMap.proj_apply, Finsupp.lapply_apply]

/-- Čech の余境界は Laurent 単項式ごとの係数に作用する。 -/
theorem projectiveLaurentCechCoordinate_differential {R : Type*} [CommRing R] {d : ℤ}
    (e : ProjectiveLaurentGlobalExponents (ι := ι) d) (k : ℕ) :
    (projectiveLaurentCechCoordinate R d e (k + 1)).comp
        (fullCechDifferential (projectiveLaurentGradedChartDiagram (ι := ι) R d) k) =
      (projectiveMonomialDifferential (projectiveLaurentNegativeSupport e.val) k).comp
        (projectiveLaurentCechCoordinate R d e k) := by
  classical
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  funext t
  simp only [LinearMap.comp_apply, projectiveMonomialDifferential_apply]
  by_cases ht : projectiveLaurentNegativeSupport e.val ⊆ cechTupleSupport t
  · rw [projectiveLaurentCechCoordinate_apply e _ _ t ht, fullCechDifferential_apply]
    change (Finsupp.lapply (projectiveLaurentLiftExponent (cechTupleSupport t) e ht) :
      (ProjectiveLaurentDegreeExponents (cechTupleSupport t) d →₀ R) →ₗ[R] R)
        (∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val • _) = _
    simp only [map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    change (Finsupp.mapDomain
      (projectiveLaurentDegreeExponentRestriction (cechTupleSupport_face_subset t i) d)
      (a (t ∘ i.succAbove))) (projectiveLaurentLiftExponent (cechTupleSupport t) e ht) = _
    rw [projectiveLaurentRestriction_coeff]
    split_ifs with hface
    · exact (projectiveLaurentCechCoordinate_apply e k a _ hface).symm
    · exact ((projectiveLaurentCechCoordinate R d e k a).property _ hface).symm
  · rw [(projectiveLaurentCechCoordinate R d e (k + 1)
      (fullCechDifferential (projectiveLaurentGradedChartDiagram (ι := ι) R d) k a)).property t ht]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [(projectiveLaurentCechCoordinate R d e k a).property _
      (fun h ↦ ht (h.trans (cechTupleSupport_face_subset t i))), smul_zero]

/-- Laurent Čech コチェインは単項式ごとの全係数で決まる。 -/
theorem projectiveLaurentCech_ext {R : Type*} [CommRing R] {d : ℤ} {k : ℕ}
    {a b : ProjectiveLaurentCochains (ι := ι) R d k}
    (h : ∀ e : ProjectiveLaurentGlobalExponents (ι := ι) d,
      projectiveLaurentCechCoordinate R d e k a = projectiveLaurentCechCoordinate R d e k b) :
    a = b := by
  funext t
  apply Finsupp.ext
  intro x
  let e := projectiveLaurentDegreeExponentEmbedding (cechTupleSupport t) d x
  have ht : projectiveLaurentNegativeSupport e.val ⊆ cechTupleSupport t :=
    (projectiveLaurentExponents_iff_negativeSupport_subset _ _).mp x.val.property
  have he := congrArg (fun z ↦ z.val t) (h e)
  rw [projectiveLaurentCechCoordinate_apply e k a t ht,
    projectiveLaurentCechCoordinate_apply e k b t ht] at he
  exact he

/-- 許される指数の単項式コチェインを、指定の係数を持つ単項式として評価する。 -/
theorem projectiveLaurentCechSingle_apply {R : Type*} [CommRing R] {d : ℤ}
    (e : ProjectiveLaurentGlobalExponents (ι := ι) d) (k : ℕ)
    (a : projectiveMonomialCochains (R := R) (projectiveLaurentNegativeSupport e.val) k)
    (t : Fin k → ι) :
    projectiveLaurentCechSingle R d e k a t =
      if ht : projectiveLaurentNegativeSupport e.val ⊆ cechTupleSupport t then
        Finsupp.single (projectiveLaurentLiftExponent (cechTupleSupport t) e ht) (a.val t)
      else 0 := by
  classical
  by_cases ht : projectiveLaurentNegativeSupport e.val ⊆ cechTupleSupport t
  · simp [projectiveLaurentCechSingle, ht, LinearMap.pi_apply]
  · simp [projectiveLaurentCechSingle, ht, LinearMap.pi_apply]

/-- 一つの単項式を入れて、その単項式の座標を取ると恒等写像になる。 -/
theorem projectiveLaurentCechCoordinate_single_self {R : Type*} [CommRing R] {d : ℤ}
    (e : ProjectiveLaurentGlobalExponents (ι := ι) d) (k : ℕ)
    (a : projectiveMonomialCochains (R := R) (projectiveLaurentNegativeSupport e.val) k) :
    projectiveLaurentCechCoordinate R d e k (projectiveLaurentCechSingle R d e k a) = a := by
  classical
  apply Subtype.ext
  funext t
  by_cases ht : projectiveLaurentNegativeSupport e.val ⊆ cechTupleSupport t
  · rw [projectiveLaurentCechCoordinate_apply e k _ t ht, projectiveLaurentCechSingle_apply,
      dite_eq_left ht, Finsupp.single_eq_same]
  · exact ((projectiveLaurentCechCoordinate R d e k _).property t ht).trans
      (a.property t ht).symm

/-- 異なる単項式の座標は零。 -/
theorem projectiveLaurentCechCoordinate_single_of_ne {R : Type*} [CommRing R] {d : ℤ}
    (e e' : ProjectiveLaurentGlobalExponents (ι := ι) d) (he : e ≠ e') (k : ℕ)
    (a : projectiveMonomialCochains (R := R) (projectiveLaurentNegativeSupport e'.val) k) :
    projectiveLaurentCechCoordinate R d e k (projectiveLaurentCechSingle R d e' k a) = 0 := by
  classical
  apply Subtype.ext
  funext t
  change (projectiveLaurentCechCoordinate R d e k _).val t = 0
  by_cases ht : projectiveLaurentNegativeSupport e.val ⊆ cechTupleSupport t
  · rw [projectiveLaurentCechCoordinate_apply e k _ t ht, projectiveLaurentCechSingle_apply]
    split_ifs with ht'
    · apply Finsupp.single_eq_of_ne
      intro h
      exact he (Subtype.ext (congrArg
        (fun x : ProjectiveLaurentDegreeExponents (cechTupleSupport t) d ↦ x.val.val) h))
    · rfl
  · exact (projectiveLaurentCechCoordinate R d e k _).property t ht

/-- 単項式コチェインの組み込みは余境界と可換。 -/
theorem projectiveLaurentCechSingle_differential {R : Type*} [CommRing R] {d : ℤ}
    (e : ProjectiveLaurentGlobalExponents (ι := ι) d) (k : ℕ) :
    (projectiveLaurentCechSingle R d e (k + 1)).comp
        (projectiveMonomialDifferential (projectiveLaurentNegativeSupport e.val) k) =
      (fullCechDifferential (projectiveLaurentGradedChartDiagram (ι := ι) R d) k).comp
        (projectiveLaurentCechSingle R d e k) := by
  apply LinearMap.ext
  intro a
  apply projectiveLaurentCech_ext
  intro e'
  simp only [LinearMap.comp_apply]
  have h := LinearMap.congr_fun (projectiveLaurentCechCoordinate_differential e' k)
    (projectiveLaurentCechSingle R d e k a)
  simp only [LinearMap.comp_apply] at h
  change _ = projectiveLaurentCechCoordinate R d e' (k + 1)
    (fullCechDifferential (projectiveLaurentGradedChartDiagram (ι := ι) R d) k
      (projectiveLaurentCechSingle R d e k a))
  rw [h]
  by_cases he : e' = e
  · subst e'
    rw [projectiveLaurentCechCoordinate_single_self, projectiveLaurentCechCoordinate_single_self]
  · rw [projectiveLaurentCechCoordinate_single_of_ne _ _ he,
      projectiveLaurentCechCoordinate_single_of_ne _ _ he, map_zero]

/-- 全タプルの有限個のチャートに現れる単項式を一つの有限集合に集める。 -/
def projectiveLaurentCechMonomialSupport {R : Type*} [CommRing R] {d : ℤ} {k : ℕ}
    (a : ProjectiveLaurentCochains (ι := ι) R d k) :
    Finset (ProjectiveLaurentGlobalExponents (ι := ι) d) := by
  classical
  exact Finset.univ.biUnion fun t : Fin k → ι ↦
    (a t).support.map (projectiveLaurentDegreeExponentEmbedding (cechTupleSupport t) d)

/-- 全チャートの台に現れない指数では座標が零。 -/
theorem projectiveLaurentCechCoordinate_eq_zero_of_notMem {R : Type*} [CommRing R] {d : ℤ} {k : ℕ}
    (a : ProjectiveLaurentCochains (ι := ι) R d k)
    (e : ProjectiveLaurentGlobalExponents (ι := ι) d)
    (he : e ∉ projectiveLaurentCechMonomialSupport a) :
    projectiveLaurentCechCoordinate R d e k a = 0 := by
  classical
  apply Subtype.ext
  funext t
  change (projectiveLaurentCechCoordinate R d e k a).val t = 0
  by_cases ht : projectiveLaurentNegativeSupport e.val ⊆ cechTupleSupport t
  · rw [projectiveLaurentCechCoordinate_apply e k a t ht]
    apply Finsupp.notMem_support_iff.mp
    intro h
    exact he (Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _,
      Finset.mem_map.mpr ⟨_, h, rfl⟩⟩)
  · exact (projectiveLaurentCechCoordinate R d e k a).property t ht

/-- 有限個の単項式の座標を足すと元の Čech コチェインになる。 -/
theorem projectiveLaurentCech_eq_sum_coordinates {R : Type*} [CommRing R] {d : ℤ} {k : ℕ}
    (a : ProjectiveLaurentCochains (ι := ι) R d k) :
    a = ∑ e ∈ projectiveLaurentCechMonomialSupport a,
      projectiveLaurentCechSingle R d e k (projectiveLaurentCechCoordinate R d e k a) := by
  classical
  apply projectiveLaurentCech_ext
  intro e
  rw [map_sum]
  by_cases he : e ∈ projectiveLaurentCechMonomialSupport a
  · rw [Finset.sum_eq_single_of_mem e he]
    · rw [projectiveLaurentCechCoordinate_single_self]
    · intro e' _ he'
      exact projectiveLaurentCechCoordinate_single_of_ne _ _ (Ne.symm he') _ _
  · rw [projectiveLaurentCechCoordinate_eq_zero_of_notMem a e he]
    symm
    apply Finset.sum_eq_zero
    intro e' he'
    exact projectiveLaurentCechCoordinate_single_of_ne _ _ (fun h : e = e' ↦ he (h.symm ▸ he')) _ _

/-- 負の指数の台が空または全体である指数を残す。 -/
def projectiveLaurentSurvives {d : ℤ} (e : ProjectiveLaurentGlobalExponents (ι := ι) d) : Prop :=
  projectiveLaurentNegativeSupport e.val = ∅ ∨ projectiveLaurentNegativeSupport e.val = Finset.univ

open scoped Classical in
/--
概要：Laurent Čech コサイクルは、台が空または全体である単項式だけで表せる。
方針：残りの各単項式を台の外の頂点で縮約し、有限和を境界として引く。
規約：長さ一では、縮約の像が長さ零の零コチェインになる。
使われ方：射影空間の捻りのコホモロジーを有限生成加群の商で表す。
-/
theorem projectiveLaurentCech_cycle_decomposition {R : Type*} [CommRing R] {d : ℤ}
    (k : ℕ) (a : ProjectiveLaurentCochains (ι := ι) R d (k + 1))
    (ha : fullCechDifferential (projectiveLaurentGradedChartDiagram (ι := ι) R d) (k + 1) a = 0) :
    ∃ b : ProjectiveLaurentCochains (ι := ι) R d k,
      (k = 0 → b = 0) ∧
      a = fullCechDifferential (projectiveLaurentGradedChartDiagram (ι := ι) R d) k b +
        ∑ e ∈ (projectiveLaurentCechMonomialSupport a).filter projectiveLaurentSurvives,
          projectiveLaurentCechSingle R d e (k + 1)
            (projectiveLaurentCechCoordinate R d e (k + 1) a) := by
  classical
  let E := projectiveLaurentCechMonomialSupport a
  have hcoord (e : ProjectiveLaurentGlobalExponents (ι := ι) d) :
      projectiveMonomialDifferential (projectiveLaurentNegativeSupport e.val) (k + 1)
        (projectiveLaurentCechCoordinate R d e (k + 1) a) = 0 := by
    have h := LinearMap.congr_fun (projectiveLaurentCechCoordinate_differential e (k + 1)) a
    simp only [LinearMap.comp_apply, ha, map_zero] at h
    exact h.symm
  have hvertex (e : ProjectiveLaurentGlobalExponents (ι := ι) d)
      (he : ¬projectiveLaurentSurvives e) : ∃ v, v ∉ projectiveLaurentNegativeSupport e.val := by
    by_contra! h
    exact he (Or.inr (Finset.eq_univ_iff_forall.mpr h))
  let b₀ (e : ProjectiveLaurentGlobalExponents (ι := ι) d) :
      projectiveMonomialCochains (R := R) (projectiveLaurentNegativeSupport e.val) k :=
    if he : ¬projectiveLaurentSurvives e then
      projectiveMonomialContraction (projectiveLaurentNegativeSupport e.val)
        (hvertex e he).choose (hvertex e he).choose_spec k
        (projectiveLaurentCechCoordinate R d e (k + 1) a)
    else 0
  let b := ∑ e ∈ E.filter (fun e ↦ ¬projectiveLaurentSurvives e),
    projectiveLaurentCechSingle R d e k (b₀ e)
  refine ⟨b, ?_, ?_⟩
  · intro hk
    subst k
    apply Finset.sum_eq_zero
    intro e he
    have hn : projectiveLaurentNegativeSupport e.val ≠ ∅ :=
      fun h ↦ (Finset.mem_filter.mp he).2 (Or.inl h)
    have hz : b₀ e = 0 := by
      apply Subtype.ext
      funext t
      apply (b₀ e).property t
      have hT : cechTupleSupport t = ∅ := by simp [cechTupleSupport]
      simpa only [hT, Finset.subset_empty] using hn
    rw [hz, map_zero]
  · have hdb (e : ProjectiveLaurentGlobalExponents (ι := ι) d)
        (he : ¬projectiveLaurentSurvives e) :
        projectiveMonomialDifferential (projectiveLaurentNegativeSupport e.val) k (b₀ e) =
          projectiveLaurentCechCoordinate R d e (k + 1) a := by
      have h := LinearMap.congr_fun (projectiveMonomialContraction_identity
        (R := R) (projectiveLaurentNegativeSupport e.val)
        (hvertex e he).choose (hvertex e he).choose_spec k)
        (projectiveLaurentCechCoordinate R d e (k + 1) a)
      simpa [LinearMap.comp_apply, hcoord e, b₀, he] using h
    have hd :
        fullCechDifferential (projectiveLaurentGradedChartDiagram (ι := ι) R d) k b =
          ∑ e ∈ E.filter (fun e ↦ ¬projectiveLaurentSurvives e),
            projectiveLaurentCechSingle R d e (k + 1)
              (projectiveLaurentCechCoordinate R d e (k + 1) a) := by
      unfold b
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro e he
      have hh := LinearMap.congr_fun (projectiveLaurentCechSingle_differential e k) (b₀ e)
      simp only [LinearMap.comp_apply] at hh
      rw [← hh, hdb e (Finset.mem_filter.mp he).2]
    rw [hd]
    have hsplit := Finset.sum_filter_add_sum_filter_not E projectiveLaurentSurvives
      (fun e ↦ projectiveLaurentCechSingle R d e (k + 1)
        (projectiveLaurentCechCoordinate R d e (k + 1) a))
    exact (projectiveLaurentCech_eq_sum_coordinates a).trans
      (hsplit.symm.trans (add_comm _ _))

/-- 固定次数で、負の指数の台が空または全体である指数は有限個。 -/
theorem finite_projectiveLaurentSurvives (d : ℤ) :
    Finite {e : ProjectiveLaurentGlobalExponents (ι := ι) d // projectiveLaurentSurvives e} := by
  classical
  let A := {e : ι → ℤ // (∀ i, 0 ≤ e i) ∧ (∑ i, e i) = d}
  let B := {e : ι → ℤ // (∀ i, e i < 0) ∧ (∑ i, e i) = d}
  let _ : Finite A := finite_projectiveCechNonnegativeExponents d
  let _ : Finite B := finite_projectiveCechNegativeExponents d
  let f : {e : ProjectiveLaurentGlobalExponents (ι := ι) d // projectiveLaurentSurvives e} →
      A ⊕ B := fun e ↦
    if h : projectiveLaurentNegativeSupport e.val.val = ∅ then
      Sum.inl ⟨e.val.val, fun i ↦ le_of_not_gt fun hi ↦ by
        have hm : i ∈ projectiveLaurentNegativeSupport e.val.val := by
          simp [projectiveLaurentNegativeSupport, hi]
        simpa [h] using hm, e.val.property⟩
    else
      Sum.inr ⟨e.val.val, fun i ↦ by
        have hu := e.property.resolve_left h
        have hm : i ∈ projectiveLaurentNegativeSupport e.val.val := hu.symm ▸ Finset.mem_univ i
        exact (Finset.mem_filter.mp hm).2, e.val.property⟩
  have hf (e : {e : ProjectiveLaurentGlobalExponents (ι := ι) d // projectiveLaurentSurvives e}) :
      Sum.elim (fun a : A ↦ a.val) (fun b : B ↦ b.val) (f e) = e.val.val := by
    dsimp only [f]
    split_ifs <;> rfl
  refine Finite.of_injective f fun e e' he ↦ Subtype.ext (Subtype.ext ?_)
  exact (hf e).symm.trans ((congrArg (Sum.elim (fun a : A ↦ a.val)
    (fun b : B ↦ b.val)) he).trans (hf e'))

/-- 台が空または全体である単項式だけを含むコチェインの部分加群。 -/
def projectiveLaurentSurvivorSubmodule (R : Type*) [CommRing R] (d : ℤ) (k : ℕ) :
    Submodule R (FullCechCochains (projectiveLaurentGradedChartDiagram (ι := ι) R d) k) :=
  ⨅ e : {e : ProjectiveLaurentGlobalExponents (ι := ι) d // ¬projectiveLaurentSurvives e},
    LinearMap.ker (projectiveLaurentCechCoordinate R d e.val k)

/-- 生き残る指数に限った Čech の各項は、Noether 環上で有限生成。 -/
theorem projectiveLaurentSurvivorSubmodule_finite (R : Type*) [CommRing R]
    [IsNoetherianRing R] (d : ℤ) (k : ℕ) :
    Module.Finite R (projectiveLaurentSurvivorSubmodule (ι := ι) R d k) := by
  classical
  let E := {e : ProjectiveLaurentGlobalExponents (ι := ι) d // projectiveLaurentSurvives e}
  let _ : Finite E := finite_projectiveLaurentSurvives d
  let f : projectiveLaurentSurvivorSubmodule (ι := ι) R d k →ₗ[R]
      (e : E) → (Fin k → ι) → R :=
    LinearMap.pi fun e ↦
      (projectiveMonomialCochains (R := R) (projectiveLaurentNegativeSupport e.val.val) k).subtype.comp
        ((projectiveLaurentCechCoordinate R d e.val k).comp
          (projectiveLaurentSurvivorSubmodule R d k).subtype)
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply projectiveLaurentCech_ext
    intro e
    by_cases he : projectiveLaurentSurvives e
    · exact Subtype.ext (congrFun h ⟨e, he⟩)
    · have hzero (c : projectiveLaurentSurvivorSubmodule (ι := ι) R d k) :
          projectiveLaurentCechCoordinate R d e k c.val = 0 := by
        exact LinearMap.mem_ker.mp (((Submodule.mem_iInf _).mp c.property) ⟨e, he⟩)
      rw [hzero a, hzero b]
  exact Module.Finite.of_injective f hf

/--
概要：指定次数の Laurent 単項式による Čech 複体のコホモロジーは有限生成。
方針：コサイクルを有限個の生き残る指数に移し、その部分加群からコホモロジーへ全射を作る。
規約：係数環は Noether。通常の非増大 Čech 複体を用いる。
使われ方：射影空間の捻りの有限性を与え、有限自由表示による降下帰納につなぐ。

これは Stacks 30.19.2 の Hⁱ の有限性に対応する射影 Čech 版の補題。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveLaurentCechHomology_finite (R : Type*) [CommRing R] [IsNoetherianRing R]
    (d : ℤ) (q : ℕ) :
    Module.Finite R ((fullCechComplex (projectiveLaurentGradedChartDiagram (ι := ι) R d)).homology q) := by
  classical
  let D := projectiveLaurentGradedChartDiagram (ι := ι) R d
  let K := fullCechComplex D
  have hd (j : ℕ) : K.d j (j + 1) = ModuleCat.ofHom (fullCechDifferential D (j + 1)) := by
    change CochainComplex.of.d (fun i ↦ ModuleCat.of R (FullCechCochains D (i + 1)))
      (fun i ↦ ModuleCat.ofHom (fullCechDifferential D (i + 1))) j (j + 1) = _
    exact CochainComplex.of_d _ _ j
  let S := K.sc q
  let V : Submodule R S.X₂ := projectiveLaurentSurvivorSubmodule R d (q + 1)
  let Z := LinearMap.ker S.g.hom
  let T := V ⊓ Z
  let _ : Module.Finite R V := projectiveLaurentSurvivorSubmodule_finite R d (q + 1)
  let j : T →ₗ[R] V := Submodule.inclusion inf_le_left
  let _ : IsNoetherian R T := isNoetherian_of_ker_bot j
    (LinearMap.ker_eq_bot.mpr (Submodule.inclusion_injective _))
  let f : T →ₗ[R] S.moduleCatLeftHomologyData.H :=
    (LinearMap.range S.moduleCatToCycles).mkQ.comp (Submodule.inclusion inf_le_right)
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range S.moduleCatToCycles) z
    have hclosed : fullCechDifferential D (q + 1) x.val = 0 := by
      have hh := x.property
      change (K.d q ((ComplexShape.up ℕ).next q)).hom x.val = 0 at hh
      rw [CochainComplex.next] at hh
      rw [hd q] at hh
      exact hh
    obtain ⟨b, hb₀, hx⟩ := projectiveLaurentCech_cycle_decomposition q x.val hclosed
    let a : S.X₂ := ∑ e ∈ (projectiveLaurentCechMonomialSupport x.val).filter projectiveLaurentSurvives,
      projectiveLaurentCechSingle R d e (q + 1)
        (projectiveLaurentCechCoordinate R d e (q + 1) x.val)
    have haV : a ∈ V := by
      change a ∈ projectiveLaurentSurvivorSubmodule (ι := ι) R d (q + 1)
      apply (Submodule.mem_iInf _).mpr
      intro e
      apply LinearMap.mem_ker.mpr
      change projectiveLaurentCechCoordinate R d e.val (q + 1)
        (∑ e' ∈ (projectiveLaurentCechMonomialSupport x.val).filter projectiveLaurentSurvives,
          projectiveLaurentCechSingle R d e' (q + 1)
            (projectiveLaurentCechCoordinate R d e' (q + 1) x.val)) = 0
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro e' he'
      exact projectiveLaurentCechCoordinate_single_of_ne _ _
        (fun h : e.val = e' ↦ e.property (h.symm ▸ (Finset.mem_filter.mp he').2)) _ _
    have hab : x.val - a ∈ LinearMap.range S.f.hom := by
      cases q with
      | zero =>
        simp only [hb₀ rfl, map_zero, zero_add] at hx
        rw [show x.val = a from hx, sub_self]
        exact Submodule.zero_mem _
      | succ q =>
        have hh : fullCechDifferential D (q + 1) b = x.val - a :=
          eq_sub_of_add_eq (by exact hx.symm)
        change x.val - a ∈ LinearMap.range
          (K.d ((ComplexShape.up ℕ).prev (q + 1)) (q + 1)).hom
        rw [CochainComplex.prev_nat_succ]
        rw [hd q]
        exact LinearMap.mem_range.mpr ⟨b, hh⟩
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hab
    have haZ : a ∈ Z := by
      apply LinearMap.mem_ker.mpr
      have h : S.g.hom (x.val - a) = 0 := hc ▸ S.moduleCat_zero_apply c
      rw [map_sub, show S.g.hom x.val = 0 from x.property, zero_sub, neg_eq_zero] at h
      exact h
    refine ⟨⟨a, haV, haZ⟩, ?_⟩
    change Submodule.Quotient.mk (⟨a, haZ⟩ : Z) = Submodule.Quotient.mk x
    symm
    apply (Submodule.Quotient.eq _).mpr
    exact ⟨c, Subtype.ext hc⟩
  let _ : Module.Finite R S.moduleCatLeftHomologyData.H := Module.Finite.of_surjective f hf
  change Module.Finite R S.homology
  exact Module.Finite.of_surjective S.moduleCatHomologyIso.inv.hom
    ((ModuleCat.epi_iff_surjective S.moduleCatHomologyIso.inv).mp inferInstance)

end Graded

end SerrePositivity.AlgebraicGeometry
