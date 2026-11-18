module

public import SerrePositivity.AlgebraicGeometry.SegreOverlapCoordinates
public import SerrePositivity.AlgebraicGeometry.DegreeOneChartCompatibility
public import SerrePositivity.AlgebraicGeometry.SegreChartInverse

/-!
概要：Segre の行・列の局所射は、二つの標準開の重なりで一致する。
方針：交叉上の単元と生成元の遷移式を、標準開の一般の比較へ渡す。
規約：次数一の評価の全射性を使い、平坦性を仮定しない。
使われ方：Segre の二つの大域の射の貼り合わせ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
variable {R A B : Type u} {ι κ : Type} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] (a : ι → A) (b : κ → B)
variable (G : ℕ → Submodule R A) [GradedRing G]
variable (H : ℕ → Submodule R B) [GradedRing H]
variable (ha : ∀ k, a k ∈ G 1) (hb : ∀ l, b l ∈ H 1)
variable (i m : ι) (j n : κ)
local instance segreCompatibilityColumnAlgebra (k : ι) :
    Algebra R (HomogeneousLocalization.Away G (a k)) := projectiveHomogeneousAwayAlgebra G (a k)
local instance segreCompatibilityRowAlgebra (l : κ) :
    Algebra R (HomogeneousLocalization.Away H (b l)) := projectiveHomogeneousAwayAlgebra H (b l)
local instance segreCompatibilityStandardAlgebra
    [GradedRing (segreCoordinateGrade (R := R) a b)] (k : ι) (l : κ) :
    Algebra R (HomogeneousLocalization.Away (segreCoordinateGrade (R := R) a b)
      (segreCoordinateProjection (R := R) a b (MvPolynomial.X (k, l)))) :=
  projectiveHomogeneousAwayAlgebra (segreCoordinateGrade (R := R) a b) _
local instance segreCompatibilityIntersectionAlgebra
    [GradedRing (segreCoordinateGrade (R := R) a b)] :
    Algebra R (HomogeneousLocalization.Away (segreCoordinateGrade (R := R) a b)
      (segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, j)) *
        segreCoordinateProjection (R := R) a b (MvPolynomial.X (m, n)))) :=
  projectiveHomogeneousAwayAlgebra (segreCoordinateGrade (R := R) a b) _

/-- 列の二つの標準開の射は、交叉から Proj A へ合成すると一致する。 -/
theorem segreColumnChart_compat (hsA : Function.Surjective (MvPolynomial.aeval (R := R) a)) :
    letI := segreCoordinateGradedRing a b G ha
    let φ := (homogeneousAwayMulRestrictionAlgHom (segreCoordinateGrade (R := R) a b)
      (segreCoordinate_denominator_mem a b m n) rfl).comp (segreColumnChartMap a b G i j ha hsA)
    let ψ := (homogeneousAwayMulRestrictionAlgHom (segreCoordinateGrade (R := R) a b)
      (segreCoordinate_denominator_mem a b i j) (mul_comm _ _)).comp
        (segreColumnChartMap a b G m n ha hsA)
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Proj.awayι G (a i) (ha i) (by decide) =
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Proj.awayι G (a m) (ha m) (by decide) := by
  let := segreCoordinateGradedRing a b G ha
  dsimp only
  apply degreeOneChart_compat_of_transition G a ha hsA (ha i) (ha m)
  · change IsUnit (HomogeneousLocalization.awayMap (segreCoordinateGrade (R := R) a b)
      (segreCoordinate_denominator_mem a b m n) rfl
      (segreColumnChartMap a b G i j ha hsA (homogeneousDegreeOneNormalize G (ha i) (a m))))
    rw [segreColumnChartMap_normalize, segreColumnFromFactor_generator]
    exact (segreOverlap_crossCoordinates_isUnit a b G ha i m j n).1
  · intro k
    change HomogeneousLocalization.awayMap (segreCoordinateGrade (R := R) a b)
      (segreCoordinate_denominator_mem a b i j) (mul_comm _ _)
      (segreColumnChartMap a b G m n ha hsA (homogeneousDegreeOneNormalize G (ha m) (a k))) *
      HomogeneousLocalization.awayMap (segreCoordinateGrade (R := R) a b)
        (segreCoordinate_denominator_mem a b m n) rfl
        (segreColumnChartMap a b G i j ha hsA (homogeneousDegreeOneNormalize G (ha i) (a m))) =
      HomogeneousLocalization.awayMap (segreCoordinateGrade (R := R) a b)
        (segreCoordinate_denominator_mem a b m n) rfl
        (segreColumnChartMap a b G i j ha hsA (homogeneousDegreeOneNormalize G (ha i) (a k)))
    rw [segreColumnChartMap_normalize, segreColumnFromFactor_generator,
      segreColumnChartMap_normalize, segreColumnFromFactor_generator,
      segreColumnChartMap_normalize, segreColumnFromFactor_generator]
    exact segreOverlap_column_transition a b G ha i m j n k

/-- 行の二つの標準開の射も、交叉から Proj B へ合成すると一致する。 -/
theorem segreRowChart_compat (hsB : Function.Surjective (MvPolynomial.aeval (R := R) b)) :
    letI := segreCoordinateGradedRing a b G ha
    let φ := (homogeneousAwayMulRestrictionAlgHom (segreCoordinateGrade (R := R) a b)
      (segreCoordinate_denominator_mem a b m n) rfl).comp (segreRowChartMap a b G H i j ha hb hsB)
    let ψ := (homogeneousAwayMulRestrictionAlgHom (segreCoordinateGrade (R := R) a b)
      (segreCoordinate_denominator_mem a b i j) (mul_comm _ _)).comp
        (segreRowChartMap a b G H m n ha hb hsB)
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Proj.awayι H (b j) (hb j) (by decide) =
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Proj.awayι H (b n) (hb n) (by decide) := by
  let := segreCoordinateGradedRing a b G ha
  dsimp only
  apply degreeOneChart_compat_of_transition H b hb hsB (hb j) (hb n)
  · change IsUnit (HomogeneousLocalization.awayMap (segreCoordinateGrade (R := R) a b)
      (segreCoordinate_denominator_mem a b m n) rfl
      (segreRowChartMap a b G H i j ha hb hsB (homogeneousDegreeOneNormalize H (hb j) (b n))))
    rw [segreRowChartMap_normalize, segreRowFromFactor_generator]
    exact (segreOverlap_crossCoordinates_isUnit a b G ha i m j n).2
  · intro l
    change HomogeneousLocalization.awayMap (segreCoordinateGrade (R := R) a b)
      (segreCoordinate_denominator_mem a b i j) (mul_comm _ _)
      (segreRowChartMap a b G H m n ha hb hsB (homogeneousDegreeOneNormalize H (hb n) (b l))) *
      HomogeneousLocalization.awayMap (segreCoordinateGrade (R := R) a b)
        (segreCoordinate_denominator_mem a b m n) rfl
        (segreRowChartMap a b G H i j ha hb hsB (homogeneousDegreeOneNormalize H (hb j) (b n))) =
      HomogeneousLocalization.awayMap (segreCoordinateGrade (R := R) a b)
        (segreCoordinate_denominator_mem a b m n) rfl
        (segreRowChartMap a b G H i j ha hb hsB (homogeneousDegreeOneNormalize H (hb j) (b l)))
    rw [segreRowChartMap_normalize, segreRowFromFactor_generator,
      segreRowChartMap_normalize, segreRowFromFactor_generator,
      segreRowChartMap_normalize, segreRowFromFactor_generator]
    exact segreOverlap_row_transition a b G ha i m j n l

end SerrePositivity.AlgebraicGeometry
