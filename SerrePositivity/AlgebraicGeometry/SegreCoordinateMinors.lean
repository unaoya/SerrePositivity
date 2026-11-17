module

public import SerrePositivity.AlgebraicGeometry.SegreNormalizedCoordinates

/-!
概要：実際の Segre 座標環での二次の関係式と正規化後の積の式。
方針：純テンソルの積の等式を実際の座標写像の核へ戻す。
規約：平坦性や非零な座標を仮定しない。
使われ方：Segre チャートの逆写像と順写像との合成の照合。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
universe u
variable {R A B : Type u} {ι κ : Type} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] (a : ι → A) (b : κ → B)

/-- 実際の Segre 座標環では 2×2 小行列式の関係式が成立する。 -/
theorem segreCoordinate_minor (i k : ι) (j l : κ) :
    segreCoordinateProjection (R := R) a b (MvPolynomial.X (k, j)) *
        segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, l)) =
      segreCoordinateProjection (R := R) a b (MvPolynomial.X (k, l)) *
        segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, j)) := by
  apply sub_eq_zero.mp
  rw [← map_mul, ← map_mul, ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change segreCoordinateMap (R := R) a b
    (MvPolynomial.X (k, j) * MvPolynomial.X (i, l) -
      MvPolynomial.X (k, l) * MvPolynomial.X (i, j)) = 0
  simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]

variable (G : ℕ → Submodule R A) [GradedRing G] (ha : ∀ i, a i ∈ G 1)

/-- 選んだ座標で正規化すると、対応する行・列の積は元の座標になる。 -/
theorem segreCoordinate_normalized_minor (i k : ι) (j l : κ) :
    letI := segreCoordinateGradedRing a b G ha
    let N := homogeneousDegreeOneNormalize (segreCoordinateGrade (R := R) a b)
      (segreCoordinate_denominator_mem a b i j)
    N (segreCoordinateProjection (R := R) a b (MvPolynomial.X (k, j))) *
        N (segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, l))) =
      N (segreCoordinateProjection (R := R) a b (MvPolynomial.X (k, l))) := by
  letI := segreCoordinateGradedRing a b G ha
  dsimp only
  have h := congrArg (homogeneousDegreeOneNormalize (segreCoordinateGrade (R := R) a b)
    (segreCoordinate_denominator_mem a b i j)) (segreCoordinate_minor a b i k j l)
  simpa only [map_mul, homogeneousDegreeOneNormalize_self, mul_one] using h

end SerrePositivity.AlgebraicGeometry
