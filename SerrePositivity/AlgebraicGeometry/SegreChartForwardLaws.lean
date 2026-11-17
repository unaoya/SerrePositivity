module

public import SerrePositivity.AlgebraicGeometry.SegreNormalizedCoordinates
public import SerrePositivity.AlgebraicGeometry.SegreRowDescent

/-!
概要：Segre チャートの順写像と正規化・因子の写像との合成の式。
方針：特殊化の合成則と、全射な次数一表示の生成元の照合を使う。
規約：元の環上の代数写像を保持し、平坦性を仮定しない。
使われ方：Segre チャートの二つの写像が互いに逆であることの照合。
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
local instance segreForwardColumnAlgebra : Algebra R (HomogeneousLocalization.Away G (a i)) :=
  projectiveHomogeneousAwayAlgebra G (a i)
local instance segreForwardRowAlgebra : Algebra R (HomogeneousLocalization.Away H (b j)) :=
  projectiveHomogeneousAwayAlgebra H (b j)

/-- Segre 座標環の正規化の後の順写像は、元の正規化された座標写像。 -/
theorem segreStandardOpenToTensor_normalize (x : SegreCoordinateRing (R := R) a b) :
    letI := segreCoordinateGradedRing a b G ha
    segreStandardOpenToTensor a b G H i j ha hb
      (homogeneousDegreeOneNormalize (segreCoordinateGrade (R := R) a b)
        (segreCoordinate_denominator_mem a b i j) x) =
      segreNormalizedCoordinateMap a b G H i j ha hb x := by
  letI := segreCoordinateGradedRing a b G ha
  apply homogeneousDegreeOneSpecialize_normalize (segreCoordinateGrade (R := R) a b)
    (segreCoordinate_denominator_mem a b i j)
  exact segreNormalizedCoordinateMap_denominator a b G H i j ha hb

/-- 列の因子写像の後の正規化された座標写像は、右因子の正規化。 -/
theorem segreNormalizedCoordinateMap_column
    (hsA : Function.Surjective (MvPolynomial.aeval (R := R) a)) (x : A) :
    segreNormalizedCoordinateMap a b G H i j ha hb (segreColumnFromFactor a b j G ha hsA x) =
      (1 : HomogeneousLocalization.Away H (b j)) ⊗ₜ[R]
        homogeneousDegreeOneNormalize G (ha i) x := by
  have he : ((segreNormalizedCoordinateMap a b G H i j ha hb).comp
      (segreColumnFromFactor a b j G ha hsA)).comp (MvPolynomial.aeval a) =
      (Algebra.TensorProduct.includeRight.comp (homogeneousDegreeOneNormalizeAlgHom G (ha i))).comp
        (MvPolynomial.aeval a) := by
    ext k
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, segreColumnFromFactor_generator,
      segreNormalizedCoordinateMap_X, homogeneousDegreeOneNormalize_self,
      Algebra.TensorProduct.includeRight_apply]
    rfl
  obtain ⟨p, rfl⟩ := hsA x
  exact AlgHom.congr_fun he p

/-- 行の因子写像の後の正規化された座標写像は、左因子の正規化。 -/
theorem segreNormalizedCoordinateMap_row
    (hsB : Function.Surjective (MvPolynomial.aeval (R := R) b)) (x : B) :
    segreNormalizedCoordinateMap a b G H i j ha hb (segreRowFromFactor a b i H hb hsB x) =
      homogeneousDegreeOneNormalize H (hb j) x ⊗ₜ[R]
        (1 : HomogeneousLocalization.Away G (a i)) := by
  have he : ((segreNormalizedCoordinateMap a b G H i j ha hb).comp
      (segreRowFromFactor a b i H hb hsB)).comp (MvPolynomial.aeval b) =
      (Algebra.TensorProduct.includeLeft.comp (homogeneousDegreeOneNormalizeAlgHom H (hb j))).comp
        (MvPolynomial.aeval b) := by
    ext l
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, segreRowFromFactor_generator,
      segreNormalizedCoordinateMap_X, homogeneousDegreeOneNormalize_self,
      Algebra.TensorProduct.includeLeft_apply]
    rfl
  obtain ⟨p, rfl⟩ := hsB x
  exact AlgHom.congr_fun he p

end SerrePositivity.AlgebraicGeometry
