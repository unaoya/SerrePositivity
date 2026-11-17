module

public import SerrePositivity.AlgebraicGeometry.DegreeOneStandardOpen
public import Mathlib.Algebra.GradedMulAction

/-!
概要：次数一の全射表示から、2f の多項式作用・有限加群性・被覆条件を供給する。
方針：元の評価の代数構造と次数保存を同時に用いる。
規約：係数環上の作用を保ち、有限性を追加仮定にしない。
使われ方：Rees・Segre と有限ファイバー冪の表示を射影 Čech の入力へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v
variable {R A : Type u} {ι : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- 元の次数一評価による多項式環上の代数構造。 -/
abbrev degreeOnePolynomialAlgebra (a : ι → A) : Algebra (MvPolynomial ι R) A :=
  (MvPolynomial.aeval (R := R) a).toAlgebra

/-- 元の評価による作用は、元の R 作用と塔をなす。 -/
theorem degreeOnePolynomial_scalarTower (a : ι → A) :
    letI := degreeOnePolynomialAlgebra (R := R) a
    IsScalarTower R (MvPolynomial ι R) A := by
  let := degreeOnePolynomialAlgebra (R := R) a
  exact IsScalarTower.of_algebraMap_eq' (MvPolynomial.aeval (R := R) a).comp_algebraMap.symm

/-- 全射評価は、同じ多項式環上の有限加群性を与える。 -/
theorem degreeOnePolynomial_finite (a : ι → A)
    (hs : Function.Surjective (MvPolynomial.aeval (R := R) a)) :
    letI := degreeOnePolynomialAlgebra (R := R) a
    Module.Finite (MvPolynomial ι R) A := by
  let := degreeOnePolynomialAlgebra (R := R) a
  exact Module.Finite.of_surjective (Algebra.linearMap _ _) hs

/-- 次数一評価による作用は、次数を保つ同じ作用である。 -/
theorem degreeOnePolynomial_gradedSMul (G : ℕ → Submodule R A) [GradedRing G]
    (a : ι → A) (ha : ∀ i, a i ∈ G 1) :
    letI := degreeOnePolynomialAlgebra (R := R) a
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G := by
  let := degreeOnePolynomialAlgebra (R := R) a
  refine ⟨?_⟩
  intro d e f x hf hx
  change MvPolynomial.aeval (R := R) a f * x ∈ G (d + e)
  exact SetLike.mul_mem_graded
    (degreeOne_aeval_mem_grade G (fun r ↦ (projectiveScalarToZero G r).property) a ha f hf) hx

/-- 同じ評価から、射影 Čech 計算の係数構造と標準開の被覆条件を同時に供給する。 -/
theorem degreeOne_projective_cech_data (G : ℕ → Submodule R A) [GradedRing G]
    (a : ι → A) (ha : ∀ i, a i ∈ G 1)
    (hs : Function.Surjective (MvPolynomial.aeval (R := R) a)) :
    letI := degreeOnePolynomialAlgebra (R := R) a
    IsScalarTower R (MvPolynomial ι R) A ∧
      SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G ∧
      Module.Finite (MvPolynomial ι R) A ∧
      (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
        (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))) := by
  let := degreeOnePolynomialAlgebra (R := R) a
  refine ⟨degreeOnePolynomial_scalarTower a, degreeOnePolynomial_gradedSMul G a ha,
    degreeOnePolynomial_finite a hs, ?_⟩
  change (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
    (Set.range (fun i : ι ↦ MvPolynomial.aeval (R := R) a (MvPolynomial.X i)))
  simpa only [MvPolynomial.aeval_X] using degreeOne_irrelevant_le_span G a ha hs

end SerrePositivity.AlgebraicGeometry
