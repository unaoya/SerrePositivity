module

public import SerrePositivity.AlgebraicGeometry.SegreChartInverse
public import SerrePositivity.AlgebraicGeometry.SegreChartForwardLaws
public import SerrePositivity.AlgebraicGeometry.DegreeOneChartExt

/-!
概要：Segre 標準開と二因子の標準開のテンソル積との実際の代数同型。
方針：正規化の全射性と生成元での外延性を使い、二つの合成を照合する。
規約：実際の全射な次数一表示を使い、平坦性や非零な分母を仮定しない。
使われ方：Proj の積の標準開による貼り合わせ。
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
local instance segreEquivColumnAlgebra : Algebra R (HomogeneousLocalization.Away G (a i)) :=
  projectiveHomogeneousAwayAlgebra G (a i)
local instance segreEquivRowAlgebra : Algebra R (HomogeneousLocalization.Away H (b j)) :=
  projectiveHomogeneousAwayAlgebra H (b j)
local instance segreEquivTargetAlgebra [GradedRing (segreCoordinateGrade (R := R) a b)] :
    Algebra R (HomogeneousLocalization.Away (segreCoordinateGrade (R := R) a b)
      (segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, j)))) :=
  projectiveHomogeneousAwayAlgebra (segreCoordinateGrade (R := R) a b)
    (segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, j)))
variable (hsA : Function.Surjective (MvPolynomial.aeval (R := R) a))
variable (hsB : Function.Surjective (MvPolynomial.aeval (R := R) b))

/-- Segre 標準開上で逆写像と順写像の合成は恒等写像。 -/
theorem segreTensorToStandardOpen_leftInverse :
    letI := segreCoordinateGradedRing a b G ha
    Function.LeftInverse (segreTensorToStandardOpen a b G H i j ha hb hsA hsB)
      (segreStandardOpenToTensor a b G H i j ha hb) := by
  letI := segreCoordinateGradedRing a b G ha
  have hsS : Function.Surjective (MvPolynomial.aeval (R := R) (fun ij : ι × κ ↦
      segreCoordinateProjection (R := R) a b (MvPolynomial.X ij))) := by
    rw [segreCoordinate_aeval]
    exact segreCoordinateProjection_surjective a b
  have he : (segreTensorToStandardOpen a b G H i j ha hb hsA hsB).comp
      (segreStandardOpenToTensor a b G H i j ha hb) =
      AlgHom.id R (HomogeneousLocalization.Away (segreCoordinateGrade (R := R) a b)
        (segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, j)))) := by
    apply degreeOneChart_algHom_ext (segreCoordinateGrade (R := R) a b)
      (segreCoordinate_denominator_mem a b i j) _ hsS
    rintro ⟨k, l⟩
    change segreTensorToStandardOpen a b G H i j ha hb hsA hsB
      (segreStandardOpenToTensor a b G H i j ha hb
        (homogeneousDegreeOneNormalize (segreCoordinateGrade (R := R) a b)
          (segreCoordinate_denominator_mem a b i j)
          (segreCoordinateProjection (R := R) a b (MvPolynomial.X (k, l))))) = _
    rw [segreStandardOpenToTensor_normalize, segreNormalizedCoordinateMap_X,
      segreTensorToStandardOpen_generators, AlgHom.id_apply]
  intro z
  exact AlgHom.congr_fun he z

/-- 二因子の標準開のテンソル積上でも、順写像と逆写像の合成は恒等写像。 -/
theorem segreTensorToStandardOpen_rightInverse :
    letI := segreCoordinateGradedRing a b G ha
    Function.RightInverse (segreTensorToStandardOpen a b G H i j ha hb hsA hsB)
      (segreStandardOpenToTensor a b G H i j ha hb) := by
  letI := segreCoordinateGradedRing a b G ha
  have hrow (z : HomogeneousLocalization.Away H (b j)) :
      segreStandardOpenToTensor a b G H i j ha hb
        (segreRowChartMap a b G H i j ha hb hsB z) =
          z ⊗ₜ[R] (1 : HomogeneousLocalization.Away G (a i)) := by
    obtain ⟨x, rfl⟩ := homogeneousDegreeOneNormalize_surjective H (hb j) z
    rw [segreRowChartMap_normalize, segreStandardOpenToTensor_normalize,
      segreNormalizedCoordinateMap_row]
  have hcol (z : HomogeneousLocalization.Away G (a i)) :
      segreStandardOpenToTensor a b G H i j ha hb
        (segreColumnChartMap a b G i j ha hsA z) =
          (1 : HomogeneousLocalization.Away H (b j)) ⊗ₜ[R] z := by
    obtain ⟨x, rfl⟩ := homogeneousDegreeOneNormalize_surjective G (ha i) z
    rw [segreColumnChartMap_normalize, segreStandardOpenToTensor_normalize,
      segreNormalizedCoordinateMap_column]
  have he : (segreStandardOpenToTensor a b G H i j ha hb).comp
      (segreTensorToStandardOpen a b G H i j ha hb hsA hsB) =
      AlgHom.id R ((HomogeneousLocalization.Away H (b j)) ⊗[R]
        (HomogeneousLocalization.Away G (a i))) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    change segreStandardOpenToTensor a b G H i j ha hb
      (segreTensorToStandardOpen a b G H i j ha hb hsA hsB (x ⊗ₜ[R] y)) = x ⊗ₜ[R] y
    rw [segreTensorToStandardOpen, Algebra.TensorProduct.lift_tmul, map_mul,
      hrow, hcol, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  intro z
  exact AlgHom.congr_fun he z

/-- 実際の Segre 標準開は、同じ基底上の二因子の標準開のテンソル積と同型。 -/
def segreStandardOpenTensorEquiv :
    letI := segreCoordinateGradedRing a b G ha
    HomogeneousLocalization.Away (segreCoordinateGrade (R := R) a b)
      (segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, j))) ≃ₐ[R]
        (HomogeneousLocalization.Away H (b j)) ⊗[R] (HomogeneousLocalization.Away G (a i)) := by
  letI := segreCoordinateGradedRing a b G ha
  exact { segreStandardOpenToTensor a b G H i j ha hb with
    invFun := segreTensorToStandardOpen a b G H i j ha hb hsA hsB
    left_inv := segreTensorToStandardOpen_leftInverse a b G H i j ha hb hsA hsB
    right_inv := segreTensorToStandardOpen_rightInverse a b G H i j ha hb hsA hsB }

end SerrePositivity.AlgebraicGeometry
