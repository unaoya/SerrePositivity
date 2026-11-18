module

public import SerrePositivity.AlgebraicGeometry.HomogeneousDegreeOneOverlap
public import SerrePositivity.AlgebraicGeometry.SegreCoordinateMinors

/-!
概要：Segre の二つの標準開の交叉での座標の遷移の法則。
方針：小行列式を制限し、交叉で単元となる座標の積を使う。
規約：平坦性・非零な分母を仮定しない。
使われ方：Segre の行・列の射の貼り合わせ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R A B : Type u} {ι κ : Type} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] (a : ι → A) (b : κ → B)
variable (G : ℕ → Submodule R A) [GradedRing G] (ha : ∀ i, a i ∈ G 1)
variable (i m : ι) (j n : κ)

/-- 最初の標準開で正規化した座標を、二つの標準開の交叉に制限する。 -/
def segreOverlapFirstCoordinate (k : ι) (l : κ) :
    letI := segreCoordinateGradedRing a b G ha
    HomogeneousLocalization.Away (segreCoordinateGrade (R := R) a b)
      (segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, j)) *
        segreCoordinateProjection (R := R) a b (MvPolynomial.X (m, n))) := by
  letI := segreCoordinateGradedRing a b G ha
  exact HomogeneousLocalization.awayMap (segreCoordinateGrade (R := R) a b)
    (segreCoordinate_denominator_mem a b m n) rfl
    (homogeneousDegreeOneNormalize (segreCoordinateGrade (R := R) a b)
      (segreCoordinate_denominator_mem a b i j)
      (segreCoordinateProjection (R := R) a b (MvPolynomial.X (k, l))))

/-- 二番目の標準開で正規化した座標を、同じ交叉に制限する。 -/
def segreOverlapSecondCoordinate (k : ι) (l : κ) :
    letI := segreCoordinateGradedRing a b G ha
    HomogeneousLocalization.Away (segreCoordinateGrade (R := R) a b)
      (segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, j)) *
        segreCoordinateProjection (R := R) a b (MvPolynomial.X (m, n))) := by
  letI := segreCoordinateGradedRing a b G ha
  exact HomogeneousLocalization.awayMap (segreCoordinateGrade (R := R) a b)
    (segreCoordinate_denominator_mem a b i j) (mul_comm _ _)
    (homogeneousDegreeOneNormalize (segreCoordinateGrade (R := R) a b)
      (segreCoordinate_denominator_mem a b m n)
      (segreCoordinateProjection (R := R) a b (MvPolynomial.X (k, l))))

/-- 正規化した小行列式の関係式は、交叉への制限でも保たれる。 -/
theorem segreOverlapFirst_minor (k : ι) (l : κ) :
    letI := segreCoordinateGradedRing a b G ha
    segreOverlapFirstCoordinate a b G ha i m j n k j *
      segreOverlapFirstCoordinate a b G ha i m j n i l =
      segreOverlapFirstCoordinate a b G ha i m j n k l := by
  let := segreCoordinateGradedRing a b G ha
  dsimp only [segreOverlapFirstCoordinate]
  exact (map_mul (HomogeneousLocalization.awayMap (segreCoordinateGrade (R := R) a b)
    (segreCoordinate_denominator_mem a b m n) rfl) _ _).symm.trans
    (congrArg (HomogeneousLocalization.awayMap (segreCoordinateGrade (R := R) a b)
      (segreCoordinate_denominator_mem a b m n) rfl)
      (segreCoordinate_normalized_minor a b G ha i k j l))

/-- 交叉では、行・列の二つの比がともに単元。 -/
theorem segreOverlap_crossCoordinates_isUnit :
    letI := segreCoordinateGradedRing a b G ha
    IsUnit (segreOverlapFirstCoordinate a b G ha i m j n m j) ∧
      IsUnit (segreOverlapFirstCoordinate a b G ha i m j n i n) := by
  let := segreCoordinateGradedRing a b G ha
  have hunit : IsUnit (segreOverlapFirstCoordinate a b G ha i m j n m n) :=
    isUnit_homogeneousDegreeOneNormalize_restrict (segreCoordinateGrade (R := R) a b)
      (segreCoordinate_denominator_mem a b i j) (segreCoordinate_denominator_mem a b m n)
  rw [← segreOverlapFirst_minor a b G ha i m j n m n] at hunit
  exact ⟨isUnit_of_mul_isUnit_left hunit, isUnit_of_mul_isUnit_right hunit⟩

/-- 二つの標準開で正規化した任意の座標の遷移の式。 -/
theorem segreOverlap_coordinate_transition (k : ι) (l : κ) :
    letI := segreCoordinateGradedRing a b G ha
    segreOverlapSecondCoordinate a b G ha i m j n k l *
      segreOverlapFirstCoordinate a b G ha i m j n m n =
      segreOverlapFirstCoordinate a b G ha i m j n k l := by
  let := segreCoordinateGradedRing a b G ha
  exact homogeneousDegreeOneRestriction_transition (segreCoordinateGrade (R := R) a b)
    (segreCoordinate_denominator_mem a b i j) (segreCoordinate_denominator_mem a b m n)
    (segreCoordinate_denominator_mem a b k l)

/-- 列の生成元は、因子の正規化の遷移式を満たす。 -/
theorem segreOverlap_column_transition (k : ι) :
    letI := segreCoordinateGradedRing a b G ha
    segreOverlapSecondCoordinate a b G ha i m j n k n *
      segreOverlapFirstCoordinate a b G ha i m j n m j =
      segreOverlapFirstCoordinate a b G ha i m j n k j := by
  let := segreCoordinateGradedRing a b G ha
  apply (segreOverlap_crossCoordinates_isUnit a b G ha i m j n).2.mul_left_inj.mp
  rw [mul_assoc, segreOverlapFirst_minor, segreOverlap_coordinate_transition,
    segreOverlapFirst_minor]

/-- 行の生成元も、同じ因子の正規化の遷移式を満たす。 -/
theorem segreOverlap_row_transition (l : κ) :
    letI := segreCoordinateGradedRing a b G ha
    segreOverlapSecondCoordinate a b G ha i m j n m l *
      segreOverlapFirstCoordinate a b G ha i m j n i n =
      segreOverlapFirstCoordinate a b G ha i m j n i l := by
  let := segreCoordinateGradedRing a b G ha
  apply (segreOverlap_crossCoordinates_isUnit a b G ha i m j n).1.mul_left_inj.mp
  calc
    _ = segreOverlapSecondCoordinate a b G ha i m j n m l *
        (segreOverlapFirstCoordinate a b G ha i m j n m j *
          segreOverlapFirstCoordinate a b G ha i m j n i n) := by ring
    _ = segreOverlapSecondCoordinate a b G ha i m j n m l *
        segreOverlapFirstCoordinate a b G ha i m j n m n := by rw [segreOverlapFirst_minor]
    _ = segreOverlapFirstCoordinate a b G ha i m j n m l :=
      segreOverlap_coordinate_transition a b G ha i m j n m l
    _ = segreOverlapFirstCoordinate a b G ha i m j n i l *
        segreOverlapFirstCoordinate a b G ha i m j n m j := by
      exact (segreOverlapFirst_minor a b G ha i m j n m l).symm.trans (mul_comm _ _)

end SerrePositivity.AlgebraicGeometry
