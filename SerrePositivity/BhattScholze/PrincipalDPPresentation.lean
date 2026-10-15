module

public import Mathlib.RingTheory.DividedPowerAlgebra.Init
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # 一元分冪表示環と任意の分冪標的への評価

既存のDividedPowerAlgebraにγ₁(1)=yを課す。
このファイルは表示環自身の分冪構造や分冪包との同型を主張しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {A : Type u} [CommRing A]

/-- 既存分冪代数内の、γ₁(1)=yを課す具体的な関係イデアル。 -/
def principalDPRelationIdeal (y : A) : Ideal (DividedPowerAlgebra A A) :=
  Ideal.span {DividedPowerAlgebra.dp A 1 (1 : A) - algebraMap A _ y}

/-- 一元yに対する具体的分冪表示環。分冪構造の存在はこの定義には含めない。 -/
abbrev PrincipalDPPresentation (A : Type u) [CommRing A] (y : A) :=
  DividedPowerAlgebra A A ⧸ principalDPRelationIdeal y

/-- 表示環内のγ_n(1)の標準像。 -/
def principalDPGenerator (y : A) (n : ℕ) : PrincipalDPPresentation A y :=
  Ideal.Quotient.mk (principalDPRelationIdeal y) (DividedPowerAlgebra.dp A n (1 : A))

/-- 課した一次関係が実商環で成立する。 -/
theorem principalDPGenerator_one (y : A) :
    principalDPGenerator y 1 = algebraMap A (PrincipalDPPresentation A y) y := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk (principalDPRelationIdeal y)
    (DividedPowerAlgebra.dp A 1 (1 : A)) -
      Ideal.Quotient.mk (principalDPRelationIdeal y)
        (algebraMap A (DividedPowerAlgebra A A) y) = 0
  rw [← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- 表示環内での、全次数の具体的階乗恒等式。 -/
theorem principalDPGenerator_factorial_mul (y : A) (n : ℕ) :
    (n.factorial : PrincipalDPPresentation A y) * principalDPGenerator y n =
      (algebraMap A (PrincipalDPPresentation A y) y) ^ n := by
  have h := congrArg (Ideal.Quotient.mk (principalDPRelationIdeal y))
    (DividedPowerAlgebra.natFactorial_mul_dp_eq (R := A) n (1 : A))
  simp only [map_mul, map_natCast, map_pow] at h
  change (n.factorial : PrincipalDPPresentation A y) * principalDPGenerator y n =
    principalDPGenerator y 1 ^ n at h
  simpa only [principalDPGenerator_one] using h

/-- 任意の分冪標的への実評価射。ねじれや正則性の仮定を置かない。 -/
def principalDPEval {B : Type v} [CommRing B] [Algebra A B]
    {I : Ideal B} (H : DividedPowers I) (y : A)
    (hy : algebraMap A B y ∈ I) : PrincipalDPPresentation A y →ₐ[A] B := by
  let g : A →ₗ[A] B := LinearMap.toSpanSingleton A B (algebraMap A B y)
  have hg : ∀ a, g a ∈ I := by
    intro a
    change a • algebraMap A B y ∈ I
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ hy
  let F := DividedPowerAlgebra.lift H g hg
  refine Ideal.Quotient.liftₐ (principalDPRelationIdeal y) F ?_
  have hker : principalDPRelationIdeal y ≤ RingHom.ker F.toRingHom := by
    apply Ideal.span_le.mpr
    rintro t (rfl : t = _)
    change F (DividedPowerAlgebra.dp A 1 (1 : A) - algebraMap A _ y) = 0
    rw [map_sub, DividedPowerAlgebra.lift_apply_dp]
    simp only [g, LinearMap.toSpanSingleton_apply_one, H.dpow_one hy, AlgHom.commutes,
      sub_self]
  intro a ha
  exact hker ha

/-- 実評価射は全標準生成元を指定した分冪値へ送る。 -/
theorem principalDPEval_generator {B : Type v} [CommRing B] [Algebra A B]
    {I : Ideal B} (H : DividedPowers I) (y : A)
    (hy : algebraMap A B y ∈ I) (n : ℕ) :
    principalDPEval H y hy (principalDPGenerator y n) = H.dpow n (algebraMap A B y) := by
  change DividedPowerAlgebra.lift H
    (LinearMap.toSpanSingleton A B (algebraMap A B y))
    (by
      intro a
      change a • algebraMap A B y ∈ I
      rw [Algebra.smul_def]
      exact I.mul_mem_left _ hy)
    (DividedPowerAlgebra.dp A n (1 : A)) = _
  rw [DividedPowerAlgebra.lift_apply_dp, LinearMap.toSpanSingleton_apply_one]

/-- 全γ_n(1)上の値は表示環からの代数射を一意に決める。 -/
theorem principalDPHom_ext {B : Type v} [CommRing B] [Algebra A B] (y : A)
    (F G : PrincipalDPPresentation A y →ₐ[A] B)
    (h : ∀ n, F (principalDPGenerator y n) = G (principalDPGenerator y n)) : F = G := by
  apply Ideal.Quotient.algHom_ext
  apply DividedPowerAlgebra.algHom_ext
  intro n a
  have ha : DividedPowerAlgebra.dp A n a =
      a ^ n • DividedPowerAlgebra.dp A n (1 : A) := by
    simpa only [smul_eq_mul, mul_one] using
      (DividedPowerAlgebra.dp_smul (R := A) (r := a) (n := n) (m := (1 : A)))
  rw [ha]
  simp only [map_smul, AlgHom.comp_apply]
  exact congrArg (fun b : B ↦ a ^ n • b) (h n)

/-- ねじれを許す任意の分冪標的に対して、指定した生成元値を持つ評価射は一意に存在する。 -/
theorem existsUnique_principalDPEval {B : Type v} [CommRing B] [Algebra A B]
    {I : Ideal B} (H : DividedPowers I) (y : A) (hy : algebraMap A B y ∈ I) :
    ∃! F : PrincipalDPPresentation A y →ₐ[A] B,
      ∀ n, F (principalDPGenerator y n) = H.dpow n (algebraMap A B y) := by
  refine ⟨principalDPEval H y hy, principalDPEval_generator H y hy, ?_⟩
  intro F hF
  apply principalDPHom_ext y
  intro n
  exact (hF n).trans (principalDPEval_generator H y hy n).symm

end SerrePositivity.BhattScholze
