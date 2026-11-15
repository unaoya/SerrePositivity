module

public import SerrePositivity.AlgebraicGeometry.ReesDegreeOneStandardOpen

/-!
概要：有限生成中心の Rees Proj に、射影 Čech の係数と標準開条件を同時供給する。
方針：構成済みの有限な次数一表示と、その実際の評価による作用を同じ証人で返す。
規約：有限な添字は Fin n。Noether 性や標準開の条件を追加仮定にしない。
使われ方：G3 のブローアップから 2f の射影四角形への接続。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

/-- 有限生成中心は 2f の射影 Čech 計算に必要な代数構造と標準開条件を同時に持つ。 -/
theorem exists_rees_projective_cech_data (hI : I.FG) :
    ∃ (n : ℕ) (a : Fin n → I),
      letI := reesDegreeOnePolynomialAlgebra I a
      IsScalarTower R (MvPolynomial (Fin n) R) (reesAlgebra I) ∧
        SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin n) R) (reesGrade I) ∧
        Module.Finite (MvPolynomial (Fin n) R) (reesAlgebra I) ∧
        (HomogeneousIdeal.irrelevant (reesGrade I)).toIdeal ≤
          Ideal.span (Set.range (fun j : Fin n ↦
            algebraMap (MvPolynomial (Fin n) R) (reesAlgebra I) (MvPolynomial.X j))) := by
  obtain ⟨n, a, ha⟩ := exists_rees_degreeOne_polynomial_surjective I hI
  refine ⟨n, a, ?_⟩
  letI := reesDegreeOnePolynomialAlgebra I a
  refine ⟨reesDegreeOnePolynomial_scalarTower I a, reesDegreeOnePolynomial_gradedSMul I a,
    reesDegreeOnePolynomial_finite I a ha, ?_⟩
  change (HomogeneousIdeal.irrelevant (reesGrade I)).toIdeal ≤
    Ideal.span (Set.range (fun j : Fin n ↦
      MvPolynomial.aeval (R := R) (fun k ↦ reesDegreeOne I (a k)) (MvPolynomial.X j)))
  simpa only [MvPolynomial.aeval_X] using reesDegreeOne_irrelevant_le_span I a ha

end SerrePositivity.AlgebraicGeometry
