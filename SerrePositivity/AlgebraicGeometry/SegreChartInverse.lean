module

public import SerrePositivity.AlgebraicGeometry.SegreRowDescent
public import SerrePositivity.AlgebraicGeometry.SegreCoordinateMinors

/-!
概要：二因子の標準開のテンソル積から Segre 標準開への実際の写像。
方針：列・行の写像を正規化して特殊化し、テンソル積の普遍性を使う。
規約：次数一評価の全射性を保持し、平坦性は仮定しない。
使われ方：Segre チャート比較の逆向きと生成元の照合。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
universe u
variable {R A B : Type u} {ι κ : Type} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] (a : ι → A) (b : κ → B)
variable (G : ℕ → Submodule R A) [GradedRing G]
variable (H : ℕ → Submodule R B) [GradedRing H]
variable (i : ι) (j : κ) (ha : ∀ k, a k ∈ G 1) (hb : ∀ l, b l ∈ H 1)
local instance segreInverseColumnAlgebra : Algebra R (HomogeneousLocalization.Away G (a i)) :=
  projectiveHomogeneousAwayAlgebra G (a i)
local instance segreInverseRowAlgebra : Algebra R (HomogeneousLocalization.Away H (b j)) :=
  projectiveHomogeneousAwayAlgebra H (b j)
local instance segreInverseTargetAlgebra [GradedRing (segreCoordinateGrade (R := R) a b)] :
    Algebra R (HomogeneousLocalization.Away (segreCoordinateGrade (R := R) a b)
    (segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, j)))) :=
  projectiveHomogeneousAwayAlgebra (segreCoordinateGrade (R := R) a b)
    (segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, j)))

variable (hsA : Function.Surjective (MvPolynomial.aeval (R := R) a))
variable (hsB : Function.Surjective (MvPolynomial.aeval (R := R) b))

/-- 列の因子写像を正規化して、因子の標準開から Segre 標準開へ特殊化する。 -/
def segreColumnChartMap :
    letI := segreCoordinateGradedRing a b G ha
    HomogeneousLocalization.Away G (a i) →ₐ[R]
    HomogeneousLocalization.Away (segreCoordinateGrade (R := R) a b)
      (segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, j))) := by
  letI := segreCoordinateGradedRing a b G ha
  exact homogeneousDegreeOneSpecializeAlgHom G (ha i)
    ((homogeneousDegreeOneNormalizeAlgHom (segreCoordinateGrade (R := R) a b)
      (segreCoordinate_denominator_mem a b i j)).comp
      (segreColumnFromFactor a b j G ha hsA)) (by
    change homogeneousDegreeOneNormalize (segreCoordinateGrade (R := R) a b)
      (segreCoordinate_denominator_mem a b i j) (segreColumnFromFactor a b j G ha hsA (a i)) = 1
    rw [segreColumnFromFactor_generator]
    exact homogeneousDegreeOneNormalize_self _ _)

/-- 列の標準開写像と因子の正規化との合成の式。 -/
theorem segreColumnChartMap_normalize (x : A) :
    letI := segreCoordinateGradedRing a b G ha
    segreColumnChartMap a b G i j ha hsA (homogeneousDegreeOneNormalize G (ha i) x) =
      homogeneousDegreeOneNormalize (segreCoordinateGrade (R := R) a b)
        (segreCoordinate_denominator_mem a b i j) (segreColumnFromFactor a b j G ha hsA x) := by
  letI := segreCoordinateGradedRing a b G ha
  apply homogeneousDegreeOneSpecialize_normalize G (ha i)
  change homogeneousDegreeOneNormalize (segreCoordinateGrade (R := R) a b)
    (segreCoordinate_denominator_mem a b i j) (segreColumnFromFactor a b j G ha hsA (a i)) = 1
  rw [segreColumnFromFactor_generator]
  exact homogeneousDegreeOneNormalize_self _ _

/-- 行の因子写像を正規化して、因子の標準開から Segre 標準開へ特殊化する。 -/
def segreRowChartMap :
    letI := segreCoordinateGradedRing a b G ha
    HomogeneousLocalization.Away H (b j) →ₐ[R]
    HomogeneousLocalization.Away (segreCoordinateGrade (R := R) a b)
      (segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, j))) := by
  letI := segreCoordinateGradedRing a b G ha
  exact homogeneousDegreeOneSpecializeAlgHom H (hb j)
    ((homogeneousDegreeOneNormalizeAlgHom (segreCoordinateGrade (R := R) a b)
      (segreCoordinate_denominator_mem a b i j)).comp
      (segreRowFromFactor a b i H hb hsB)) (by
    change homogeneousDegreeOneNormalize (segreCoordinateGrade (R := R) a b)
      (segreCoordinate_denominator_mem a b i j) (segreRowFromFactor a b i H hb hsB (b j)) = 1
    rw [segreRowFromFactor_generator]
    exact homogeneousDegreeOneNormalize_self _ _)

/-- 行の標準開写像と因子の正規化との合成の式。 -/
theorem segreRowChartMap_normalize (x : B) :
    letI := segreCoordinateGradedRing a b G ha
    segreRowChartMap a b G H i j ha hb hsB (homogeneousDegreeOneNormalize H (hb j) x) =
      homogeneousDegreeOneNormalize (segreCoordinateGrade (R := R) a b)
        (segreCoordinate_denominator_mem a b i j) (segreRowFromFactor a b i H hb hsB x) := by
  letI := segreCoordinateGradedRing a b G ha
  apply homogeneousDegreeOneSpecialize_normalize H (hb j)
  change homogeneousDegreeOneNormalize (segreCoordinateGrade (R := R) a b)
    (segreCoordinate_denominator_mem a b i j) (segreRowFromFactor a b i H hb hsB (b j)) = 1
  rw [segreRowFromFactor_generator]
  exact homogeneousDegreeOneNormalize_self _ _

/-- 二因子の標準開から Segre 標準開への実際のテンソル積の代数写像。 -/
def segreTensorToStandardOpen :
    letI := segreCoordinateGradedRing a b G ha
    (HomogeneousLocalization.Away H (b j)) ⊗[R] (HomogeneousLocalization.Away G (a i)) →ₐ[R]
      HomogeneousLocalization.Away (segreCoordinateGrade (R := R) a b)
        (segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, j))) := by
  letI := segreCoordinateGradedRing a b G ha
  exact Algebra.TensorProduct.lift (segreRowChartMap a b G H i j ha hb hsB)
    (segreColumnChartMap a b G i j ha hsA) (fun _ _ ↦ Commute.all _ _)

/-- 逆向きの写像は正規化した二生成元の純テンソルを同じ座標へ送る。 -/
theorem segreTensorToStandardOpen_generators (k : ι) (l : κ) :
    letI := segreCoordinateGradedRing a b G ha
    segreTensorToStandardOpen a b G H i j ha hb hsA hsB
      (homogeneousDegreeOneNormalize H (hb j) (b l) ⊗ₜ[R]
        homogeneousDegreeOneNormalize G (ha i) (a k)) =
      homogeneousDegreeOneNormalize (segreCoordinateGrade (R := R) a b)
        (segreCoordinate_denominator_mem a b i j)
        (segreCoordinateProjection (R := R) a b (MvPolynomial.X (k, l))) := by
  letI := segreCoordinateGradedRing a b G ha
  rw [segreTensorToStandardOpen, Algebra.TensorProduct.lift_tmul,
    segreRowChartMap_normalize, segreColumnChartMap_normalize,
    segreRowFromFactor_generator, segreColumnFromFactor_generator, mul_comm]
  exact segreCoordinate_normalized_minor a b G ha i k j l

end SerrePositivity.AlgebraicGeometry
