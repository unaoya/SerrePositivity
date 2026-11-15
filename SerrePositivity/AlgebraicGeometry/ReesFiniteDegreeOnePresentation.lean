module

public import SerrePositivity.AlgebraicGeometry.Blowup
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Finiteness.Basic

/-!
概要：有限生成中心の Rees 代数を有限個の次数一元で表示する。
方針：中心の有限生成加群としての生成族を線形に送り、既存の次数一生成性を使う。
規約：有限な添字は Fin n で Type 0。Noether 性は要求しない。
使われ方：G3 のブローアップを射影 Čech の有限多項式表示へ渡す入口。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open Polynomial
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

/-- 既存の次数一元を、中心イデアルからの線形写像として扱う。 -/
def reesDegreeOneLinearMap : I →ₗ[R] reesAlgebra I :=
  (((monomial 1 : R →ₗ[R] R[X]).comp I.subtype).codRestrict (reesAlgebra I).toSubmodule
    (fun a ↦ reesAlgebra.monomial_mem.mpr (by simpa using a.property)))

@[simp]
theorem reesDegreeOneLinearMap_apply (a : I) :
    reesDegreeOneLinearMap I a = reesDegreeOne I a := rfl

/-- 有限生成中心の Rees 代数は、ある有限個の実際の次数一元で生成される。 -/
theorem exists_rees_finite_degreeOne_generators (hI : I.FG) :
    ∃ (n : ℕ) (a : Fin n → I),
      Algebra.adjoin R (Set.range (fun j ↦ reesDegreeOne I (a j))) = ⊤ := by
  letI : Module.Finite R I := Module.Finite.of_fg hI
  obtain ⟨n, a, ha⟩ := Module.Finite.exists_fin (R := R) (M := I)
  let B := Algebra.adjoin R (Set.range (fun j ↦ reesDegreeOne I (a j)))
  let T := B.toSubmodule.comap (reesDegreeOneLinearMap I)
  have hT : T = ⊤ := by
    apply top_unique
    rw [← ha]
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact Algebra.subset_adjoin ⟨j, rfl⟩
  refine ⟨n, a, ?_⟩
  change B = ⊤
  apply top_unique
  rw [← rees_adjoin_degreeOne I]
  apply Algebra.adjoin_le
  rintro x ⟨b, rfl⟩
  change b ∈ T
  rw [hT]
  trivial

/-- 同じ有限族による多項式評価は Rees 代数への全射。 -/
theorem exists_rees_degreeOne_polynomial_surjective (hI : I.FG) :
    ∃ (n : ℕ) (a : Fin n → I),
      Function.Surjective (MvPolynomial.aeval (R := R) (fun j ↦ reesDegreeOne I (a j))) := by
  obtain ⟨n, a, ha⟩ := exists_rees_finite_degreeOne_generators I hI
  refine ⟨n, a, ?_⟩
  intro x
  have h : (MvPolynomial.aeval (R := R) (fun j ↦ reesDegreeOne I (a j))).range = ⊤ := by
    rw [MvPolynomial.aeval_range, ha]
  have hx : x ∈ (MvPolynomial.aeval (R := R) (fun j ↦ reesDegreeOne I (a j))).range := by
    rw [h]
    trivial
  exact hx

end SerrePositivity.AlgebraicGeometry
