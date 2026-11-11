module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedChart
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
概要：自然数次数の加群を、負の次数の成分が零である整数次数の加群へ移す。
方針：直和の自然数添字を整数へ埋め、負の成分の元は零として扱う。
規約：多項式環の整数次数は全指数の和。
使われ方：Proj で使う自然数次数の加群を、捻りを含む Čech 計算へ接続する。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory
open scoped DirectSum

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- 自然数次数の加群を、負の次数では零として整数次数へ延ばす。 -/
def projectiveNatGradingInt (G : ℕ → Submodule R M) (d : ℤ) : Submodule R M :=
  if 0 ≤ d then G d.toNat else ⊥

@[simp]
theorem projectiveNatGradingInt_natCast (G : ℕ → Submodule R M) (n : ℕ) :
    projectiveNatGradingInt G (n : ℤ) = G n := by
  simp [projectiveNatGradingInt]

/-- 自然数次数の一つの成分を、整数次数の同じ成分に入れる。 -/
def projectiveNatGradingPieceMap (G : ℕ → Submodule R M) (n : ℕ) :
    G n →+ projectiveNatGradingInt G (n : ℤ) where
  toFun x := ⟨x.val, by simpa using x.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- 直和の自然数添字を整数へ埋める。 -/
def projectiveNatGradingDirectSumMap (G : ℕ → Submodule R M) :
    (⨁ n, G n) →+ ⨁ d, projectiveNatGradingInt G d :=
  DirectSum.toAddMonoid fun n ↦
    (DirectSum.of (fun d ↦ projectiveNatGradingInt G d) (n : ℤ)).comp
      (projectiveNatGradingPieceMap G n)

/-- 負の成分を零にしても、元の加群の次数分解が得られる。 -/
@[instance_reducible]
def projectiveNatGradingIntDecomposition (G : ℕ → Submodule R M) [DirectSum.Decomposition G] :
    DirectSum.Decomposition (projectiveNatGradingInt G) := by
  classical
  let H := projectiveNatGradingInt G
  let d (x : M) := projectiveNatGradingDirectSumMap G (DirectSum.decompose G x)
  have hsum (z : ⨁ n, G n) :
      DirectSum.coeAddMonoidHom H (projectiveNatGradingDirectSumMap G z) =
        DirectSum.coeAddMonoidHom G z := by
    induction z using DirectSum.induction_on with
    | zero => simp
    | of n x =>
      dsimp only [H]
      simp only [projectiveNatGradingDirectSumMap, DirectSum.toAddMonoid_of,
        AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  refine { decompose' := d, left_inv := ?_, right_inv := ?_ }
  · intro x
    change DirectSum.coeAddMonoidHom H
      (projectiveNatGradingDirectSumMap G (DirectSum.decompose G x)) = x
    rw [hsum]
    exact (DirectSum.decompose G).left_inv x
  · intro z
    induction z using DirectSum.induction_on with
    | zero => simp [d]
    | of i x =>
      rw [DirectSum.coeAddMonoidHom_of]
      cases i with
      | ofNat n =>
        have hx : x.val ∈ G n := by
          have hm := x.property
          change x.val ∈ projectiveNatGradingInt G (n : ℤ) at hm
          simpa [projectiveNatGradingInt] using hm
        change projectiveNatGradingDirectSumMap G (DirectSum.decompose G x.val) = _
        rw [DirectSum.decompose_of_mem G hx]
        simp only [projectiveNatGradingDirectSumMap, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]
        rfl
      | negSucc n =>
        have hx : x = 0 := by
          apply Subtype.ext
          change x.val = 0
          have hle : projectiveNatGradingInt G (Int.negSucc n) ≤ (⊥ : Submodule R M) := by
            simp [projectiveNatGradingInt]
          exact hle x.property
        rw [hx]
        simp [d]
    | add x y hx hy =>
      simp only [map_add, d, DirectSum.decompose_add] at hx hy ⊢
      rw [hx, hy]

section Polynomial

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]

/-- 整数としての多項式の次数は、自然数としての指数の次数の埋め込み。 -/
theorem projectivePolynomialDegree_eq_natCast (e : ι →₀ ℕ) :
    projectivePolynomialDegree e = (e.degree : ℤ) := by
  simp [projectivePolynomialDegree, Finsupp.degree_eq_sum, Nat.cast_sum]

/-- 自然数次数では、多項式の整数次数成分と標準的な斉次成分が一致する。 -/
theorem projectivePolynomialGrade_natCast (n : ℕ) :
    AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)) (n : ℤ) =
      MvPolynomial.homogeneousSubmodule ι R n := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  apply Submodule.ext
  intro p
  change (∀ e ∈ p.coeff.support, projectivePolynomialDegree e = (n : ℤ)) ↔
    (∀ e ∈ p.coeff.support, e.degree = n)
  simp only [projectivePolynomialDegree_eq_natCast, Int.natCast_inj]

/-- 負の次数の多項式は零。 -/
theorem projectivePolynomialGrade_eq_bot_of_neg (d : ℤ) (hd : d < 0) :
    AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)) d = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro p hp
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro e
  change p.coeff e = 0
  by_contra he
  have h := hp e (Finsupp.mem_support_iff.mpr he)
  rw [projectivePolynomialDegree_eq_natCast] at h
  have hn := Int.natCast_nonneg e.degree
  omega

/-- 自然数次数の多項式作用は、零で延ばした整数次数の加群にも作用する。 -/
theorem projectiveNatGradingIntSMul (G : ℕ → Submodule R M)
    [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G] :
    SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt G) := by
  refine ⟨?_⟩
  intro i j a m ha hm
  by_cases hi : 0 ≤ i
  · by_cases hj : 0 ≤ j
    · have hgrade :
          AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)) i =
            MvPolynomial.homogeneousSubmodule ι R i.toNat := by
        calc
          AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)) i =
              AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)) (i.toNat : ℤ) :=
            congrArg (fun k ↦ AddMonoidAlgebra.gradeBy R
              (projectivePolynomialDegree (ι := ι)) k) (Int.toNat_of_nonneg hi).symm
          _ = _ := projectivePolynomialGrade_natCast (R := R) (ι := ι) i.toNat
      have hai : a ∈ MvPolynomial.homogeneousSubmodule ι R i.toNat := hgrade ▸ ha
      have hmj : m ∈ G j.toNat := by simpa [projectiveNatGradingInt, hj] using hm
      have h := SetLike.GradedSMul.smul_mem hai hmj
      change a • m ∈ projectiveNatGradingInt G (i + j)
      simpa [projectiveNatGradingInt, add_nonneg hi hj, Int.toNat_add hi hj] using h
    · have hmzero : m = 0 := by simpa [projectiveNatGradingInt, hj] using hm
      simp only [hmzero, smul_zero]
      exact Submodule.zero_mem _
  · have hazero : a = 0 := by
      rw [projectivePolynomialGrade_eq_bot_of_neg (R := R) (ι := ι) i (lt_of_not_ge hi)] at ha
      exact ha
    simp only [hazero, zero_smul]
    exact Submodule.zero_mem _

/-- 自然数次数の加群の標準開係数図式を、整数次数へ延ばして作る。 -/
def projectiveNatGradedModuleChartDiagram (G : ℕ → Submodule R M)
    [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G] (d : ℤ) :
    Finset ι ⥤ ModuleCat R := by
  letI := projectiveNatGradingIntSMul (ι := ι) G
  exact projectiveGradedModuleChartDiagram (ι := ι) (projectiveNatGradingInt G) d

end Polynomial

end SerrePositivity.AlgebraicGeometry
