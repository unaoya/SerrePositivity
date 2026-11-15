module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
概要：多項式環の次数零の斉次成分を、元の係数環と実際の環同型で比較する。
方針：定数多項式の射を作り、次数零成分が係数の像であることを使う。
規約：次数による grading の instance は局所に指定する。
使われ方：C05 の Proj の固有な構造射の基底を Spec R に戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) (ι : Type u) [CommRing R]

/-- 係数を次数零の定数多項式へ送る実際の環写像。 -/
def polynomialGradeZeroMap : R →+* MvPolynomial.homogeneousSubmodule ι R 0 where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C ι r⟩
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_mul' x y := Subtype.ext (map_mul MvPolynomial.C x y)
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_add' x y := Subtype.ext (map_add MvPolynomial.C x y)

/-- 多項式環の次数零成分は、定数多項式の射によって係数環と環同型。 -/
def polynomialGradeZeroEquiv : R ≃+* MvPolynomial.homogeneousSubmodule ι R 0 :=
  RingEquiv.ofBijective (polynomialGradeZeroMap R ι) (by
    constructor
    · intro x y h
      exact MvPolynomial.C_injective ι R (congrArg Subtype.val h)
    · rintro ⟨p, hp⟩
      rw [MvPolynomial.homogeneousSubmodule_zero, Submodule.mem_one] at hp
      obtain ⟨r, hr⟩ := hp
      refine ⟨r, Subtype.ext ?_⟩
      change MvPolynomial.C r = p
      simpa only [MvPolynomial.algebraMap_eq] using hr)

/-- 同型の順射は指定した定数多項式の射と一致する。 -/
theorem polynomialGradeZeroEquiv_apply (r : R) :
    (polynomialGradeZeroEquiv R ι r : MvPolynomial ι R) = MvPolynomial.C r := rfl

end SerrePositivity.AlgebraicGeometry
