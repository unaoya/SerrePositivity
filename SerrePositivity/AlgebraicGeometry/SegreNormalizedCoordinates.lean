module

public import SerrePositivity.AlgebraicGeometry.HomogeneousDegreeOneAlgebraMaps
public import SerrePositivity.AlgebraicGeometry.SegreCoordinateStandardOpen

/-!
概要：Segre 座標環から二つの標準開のテンソル積への実際の写像。
方針：二因子の正規化のテンソル積を座標写像と合成し、同じ核による商へ降ろす。
規約：平坦性と次数一生成を仮定しない。ここでは逆写像はまだ主張しない。
使われ方：Segre 標準開のチャート比較の順方向。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
universe u
variable {R A B C : Type u} {ι κ : Type} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] (a : ι → A) (b : κ → B)

/-- 座標写像の後の任意の代数写像は、同じ Segre 座標環へ降りる。 -/
def segreCoordinateDescend [CommRing C] [Algebra R C] (ψ : B ⊗[R] A →ₐ[R] C) :
    SegreCoordinateRing (R := R) a b →ₐ[R] C :=
  Ideal.Quotient.liftₐ _ (ψ.comp (segreCoordinateMap (R := R) a b)) (by
    intro p hp
    change ψ (segreCoordinateMap (R := R) a b p) = 0
    rw [show segreCoordinateMap (R := R) a b p = 0 from hp, map_zero])

/-- 商写像の後の降下は元の合成に一致する。 -/
theorem segreCoordinateDescend_projection [CommRing C] [Algebra R C]
    (ψ : B ⊗[R] A →ₐ[R] C) (p : MvPolynomial (ι × κ) R) :
    segreCoordinateDescend a b ψ (segreCoordinateProjection (R := R) a b p) =
      ψ (segreCoordinateMap (R := R) a b p) := rfl

variable (G : ℕ → Submodule R A) [GradedRing G]
variable (H : ℕ → Submodule R B) [GradedRing H]
variable (i : ι) (j : κ) (ha : ∀ i, a i ∈ G 1) (hb : ∀ j, b j ∈ H 1)
local instance : Algebra R (HomogeneousLocalization.Away G (a i)) :=
  projectiveHomogeneousAwayAlgebra G (a i)
local instance : Algebra R (HomogeneousLocalization.Away H (b j)) :=
  projectiveHomogeneousAwayAlgebra H (b j)

/-- 同じ核で降ろした、二つの正規化チャートのテンソル積への代数写像。 -/
def segreNormalizedCoordinateMap : SegreCoordinateRing (R := R) a b →ₐ[R]
    (HomogeneousLocalization.Away H (b j)) ⊗[R] (HomogeneousLocalization.Away G (a i)) :=
  segreCoordinateDescend a b
    (Algebra.TensorProduct.map (homogeneousDegreeOneNormalizeAlgHom H (hb j))
      (homogeneousDegreeOneNormalizeAlgHom G (ha i)))

/-- 座標の像は、二因子の正規化された座標の純テンソル。 -/
theorem segreNormalizedCoordinateMap_X (k : ι) (l : κ) :
    segreNormalizedCoordinateMap a b G H i j ha hb
      (segreCoordinateProjection (R := R) a b (MvPolynomial.X (k, l))) =
      homogeneousDegreeOneNormalize H (hb j) (b l) ⊗ₜ[R]
        homogeneousDegreeOneNormalize G (ha i) (a k) := by
  rw [segreNormalizedCoordinateMap, segreCoordinateDescend_projection, segreCoordinateMap_X,
    Algebra.TensorProduct.map_tmul]
  rfl

/-- 選んだ標準開の分母は 1 に移る。 -/
theorem segreNormalizedCoordinateMap_denominator :
    segreNormalizedCoordinateMap a b G H i j ha hb
      (segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, j))) = 1 := by
  rw [segreNormalizedCoordinateMap_X, homogeneousDegreeOneNormalize_self,
    homogeneousDegreeOneNormalize_self]
  exact Algebra.TensorProduct.one_def.symm

/-- 選んだ Segre 座標は実際の商の次数一成分に入る。 -/
theorem segreCoordinate_denominator_mem :
    segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, j)) ∈
      segreCoordinateGrade (R := R) a b 1 :=
  segreCoordinateProjection_preservesPiece a b _
    ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X R (i, j)))

/-- 選んだ Segre 標準開から二因子の標準開のテンソル積への実際の代数写像。 -/
def segreStandardOpenToTensor :
    letI := segreCoordinateGradedRing a b G ha
    letI := projectiveHomogeneousAwayAlgebra (segreCoordinateGrade (R := R) a b)
      (segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, j)))
    HomogeneousLocalization.Away (segreCoordinateGrade (R := R) a b)
      (segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, j))) →ₐ[R]
        (HomogeneousLocalization.Away H (b j)) ⊗[R] (HomogeneousLocalization.Away G (a i)) := by
  letI := segreCoordinateGradedRing a b G ha
  letI := projectiveHomogeneousAwayAlgebra (segreCoordinateGrade (R := R) a b)
    (segreCoordinateProjection (R := R) a b (MvPolynomial.X (i, j)))
  exact homogeneousDegreeOneSpecializeAlgHom (segreCoordinateGrade (R := R) a b)
    (segreCoordinate_denominator_mem a b i j)
    (segreNormalizedCoordinateMap a b G H i j ha hb)
    (segreNormalizedCoordinateMap_denominator a b G H i j ha hb)

end SerrePositivity.AlgebraicGeometry
