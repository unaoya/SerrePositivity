module

public import SerrePositivity.AlgebraicGeometry.SegreProjectiveProjections

/-!
概要：Segre の二つの大域射による標準開の逆像。
方針：全標準開で正規化した座標を計算し、小行列式の関係を使う。
規約：平坦性・Noether 性・非零の座標を仮定しない。
使われ方：実際のファイバー積との比較を二つの因子の標準開上で行う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
variable {R A B : Type u} {ι κ : Type} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] (a : ι → A) (b : κ → B)
variable (G : ℕ → Submodule R A) [GradedRing G] (ha : ∀ k, a k ∈ G 1)
variable (H : ℕ → Submodule R B) [GradedRing H] (hb : ∀ l, b l ∈ H 1)
local notation "SG" => segreCoordinateGrade (R := R) a b
local notation "z" => (fun p : ι × κ ↦ segreCoordinateProjection (R := R) a b (MvPolynomial.X p))
local instance segrePreimageColumnAlgebra (x : A) :
    Algebra R (HomogeneousLocalization.Away G x) := projectiveHomogeneousAwayAlgebra G x
local instance segrePreimageRowAlgebra (x : B) :
    Algebra R (HomogeneousLocalization.Away H x) := projectiveHomogeneousAwayAlgebra H x
local instance segrePreimageStandardAlgebra [GradedRing SG]
    (x : SegreCoordinateRing (R := R) a b) :
    Algebra R (HomogeneousLocalization.Away SG x) := projectiveHomogeneousAwayAlgebra SG x

/-- 最初の因子の標準開の逆像を、Segre の一つの標準開上で計算する。 -/
theorem segreLeftProjection_chart_preimage_basicOpen
    (hsA : Function.Surjective (MvPolynomial.aeval (R := R) a)) (i k : ι) (j : κ) :
    letI := segreCoordinateGradedRing a b G ha
    Proj.awayι SG (z (i, j)) (segreCoordinate_denominator_mem a b i j) (by decide) ⁻¹ᵁ
      (segreLeftProjection a b G ha hsA ⁻¹ᵁ Proj.basicOpen G (a k)) =
      PrimeSpectrum.basicOpen (homogeneousDegreeOneNormalize SG
        (segreCoordinate_denominator_mem a b i j) (z (k, j))) := by
  let := segreCoordinateGradedRing a b G ha
  rw [← Scheme.Hom.comp_preimage, segreLeftProjection_awayι, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen G (ha i) (by decide) (ha k) (by decide),
    ← homogeneousDegreeOneNormalize_eq_isLocalizationElem G (ha i) (ha k),
    SpecMap_preimage_basicOpen]
  change PrimeSpectrum.basicOpen (segreColumnChartMap a b G i j ha hsA
    (homogeneousDegreeOneNormalize G (ha i) (a k))) = _
  rw [segreColumnChartMap_normalize, segreColumnFromFactor_generator]

/-- 二番目の因子の標準開も、同じ Segre 標準開上で正規化した座標で切り出される。 -/
theorem segreRightProjection_chart_preimage_basicOpen
    (hsB : Function.Surjective (MvPolynomial.aeval (R := R) b)) (i : ι) (j l : κ) :
    letI := segreCoordinateGradedRing a b G ha
    Proj.awayι SG (z (i, j)) (segreCoordinate_denominator_mem a b i j) (by decide) ⁻¹ᵁ
      (segreRightProjection a b G ha H hb hsB ⁻¹ᵁ Proj.basicOpen H (b l)) =
      PrimeSpectrum.basicOpen (homogeneousDegreeOneNormalize SG
        (segreCoordinate_denominator_mem a b i j) (z (i, l))) := by
  let := segreCoordinateGradedRing a b G ha
  rw [← Scheme.Hom.comp_preimage, segreRightProjection_awayι, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen H (hb j) (by decide) (hb l) (by decide),
    ← homogeneousDegreeOneNormalize_eq_isLocalizationElem H (hb j) (hb l),
    SpecMap_preimage_basicOpen]
  change PrimeSpectrum.basicOpen (segreRowChartMap a b G H i j ha hb hsB
    (homogeneousDegreeOneNormalize H (hb j) (b l))) = _
  rw [segreRowChartMap_normalize, segreRowFromFactor_generator]

/-- 二つの因子の標準開の逆像の交叉は、同じ座標の基本開となる。 -/
theorem segreProjection_chart_preimage_pair
    (hsA : Function.Surjective (MvPolynomial.aeval (R := R) a))
    (hsB : Function.Surjective (MvPolynomial.aeval (R := R) b)) (i k : ι) (j l : κ) :
    letI := segreCoordinateGradedRing a b G ha
    Proj.awayι SG (z (i, j)) (segreCoordinate_denominator_mem a b i j) (by decide) ⁻¹ᵁ
      ((segreLeftProjection a b G ha hsA ⁻¹ᵁ Proj.basicOpen G (a k)) ⊓
        (segreRightProjection a b G ha H hb hsB ⁻¹ᵁ Proj.basicOpen H (b l))) =
      PrimeSpectrum.basicOpen (homogeneousDegreeOneNormalize SG
        (segreCoordinate_denominator_mem a b i j) (z (k, l))) := by
  let := segreCoordinateGradedRing a b G ha
  rw [Scheme.Hom.preimage_inf, segreLeftProjection_chart_preimage_basicOpen,
    segreRightProjection_chart_preimage_basicOpen]
  exact (PrimeSpectrum.basicOpen_mul
    (homogeneousDegreeOneNormalize SG (segreCoordinate_denominator_mem a b i j) (z (k, j)))
    (homogeneousDegreeOneNormalize SG
      (segreCoordinate_denominator_mem a b i j) (z (i, l)))).symm.trans
      (congrArg PrimeSpectrum.basicOpen (segreCoordinate_normalized_minor a b G ha i k j l))

set_option backward.isDefEq.respectTransparency false in
/-- 二つの因子の標準開の逆像の交叉は、Segre の対応する標準開そのもの。 -/
theorem segreProjection_preimage_pair
    (hsA : Function.Surjective (MvPolynomial.aeval (R := R) a))
    (hsB : Function.Surjective (MvPolynomial.aeval (R := R) b)) (k : ι) (l : κ) :
    letI := segreCoordinateGradedRing a b G ha
    (segreLeftProjection a b G ha hsA ⁻¹ᵁ Proj.basicOpen G (a k)) ⊓
      (segreRightProjection a b G ha H hb hsB ⁻¹ᵁ Proj.basicOpen H (b l)) =
      Proj.basicOpen SG (z (k, l)) := by
  let := segreCoordinateGradedRing a b G ha
  apply TopologicalSpace.Opens.ext
  ext x
  obtain ⟨p, y, rfl⟩ := (segreProjectiveOpenCover a b G ha).openCover.exists_eq x
  have h := segreProjection_chart_preimage_pair a b G ha H hb hsA hsB p.1 k p.2 l
  rw [homogeneousDegreeOneNormalize_eq_isLocalizationElem SG
    (segreCoordinate_denominator_mem a b p.1 p.2)
    (segreCoordinate_denominator_mem a b k l),
    ← Proj.awayι_preimage_basicOpen SG (segreCoordinate_denominator_mem a b p.1 p.2)
      (by decide) (segreCoordinate_denominator_mem a b k l) (by decide)] at h
  exact (congrArg (fun U ↦ y ∈ U) h).to_iff

end SerrePositivity.AlgebraicGeometry
