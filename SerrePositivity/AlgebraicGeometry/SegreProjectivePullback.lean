module

public import SerrePositivity.AlgebraicGeometry.SegreProjectivePreimage
public import SerrePositivity.AlgebraicGeometry.SegreChartPullback
public import SerrePositivity.AlgebraicGeometry.PairOpenCoverPullback
public import SerrePositivity.AlgebraicGeometry.DegreeOneStandardOpen

/-!
概要：実際の Segre の Proj は、同じ Spec R 上の二つの因子のファイバー積。
方針：二つの因子の次数一被覆と Segre 標準開の Cartesian 四角形を貼り合わせる。
規約：元の全射な次数一表示を使い、平坦性・Noether 性を仮定しない。
使われ方：射影 Čech の有限ファイバー冪の次数一表示。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {R A B : Type u} {ι κ : Type} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] (a : ι → A) (b : κ → B)
variable (G : ℕ → Submodule R A) [GradedRing G] (ha : ∀ k, a k ∈ G 1)
variable (H : ℕ → Submodule R B) [GradedRing H] (hb : ∀ l, b l ∈ H 1)
local notation "SG" => segreCoordinateGrade (R := R) a b
local notation "z" => (fun p : ι × κ ↦ segreCoordinateProjection (R := R) a b (MvPolynomial.X p))
local instance segreGlobalPullbackColumnAlgebra (x : A) :
    Algebra R (HomogeneousLocalization.Away G x) := projectiveHomogeneousAwayAlgebra G x
local instance segreGlobalPullbackRowAlgebra (x : B) :
    Algebra R (HomogeneousLocalization.Away H x) := projectiveHomogeneousAwayAlgebra H x
local instance segreGlobalPullbackStandardAlgebra [GradedRing SG]
    (x : SegreCoordinateRing (R := R) a b) :
    Algebra R (HomogeneousLocalization.Away SG x) := projectiveHomogeneousAwayAlgebra SG x

set_option backward.isDefEq.respectTransparency false in
/-- 実際の二つの Segre 大域射は、同じ Spec R 上の pullback を与える。 -/
theorem isPullback_segreProjectiveProjections
    (hsA : Function.Surjective (MvPolynomial.aeval (R := R) a))
    (hsB : Function.Surjective (MvPolynomial.aeval (R := R) b)) :
    letI := segreCoordinateGradedRing a b G ha
    IsPullback (segreLeftProjection a b G ha hsA)
      (segreRightProjection a b G ha H hb hsB)
      (projectiveCechStructureMap G) (projectiveCechStructureMap H) := by
  let := segreCoordinateGradedRing a b G ha
  let 𝒰 := (Proj.affineOpenCoverOfIrrelevantLESpan G a ha
    (fun _ ↦ by decide : ∀ _ : ι, 0 < 1) (degreeOne_irrelevant_le_span G a ha hsA)).openCover
  let 𝒱 := (Proj.affineOpenCoverOfIrrelevantLESpan H b hb
    (fun _ ↦ by decide : ∀ _ : κ, 0 < 1) (degreeOne_irrelevant_le_span H b hb hsB)).openCover
  refine isPullback_of_pairOpenCover _ _ _ _ 𝒰 𝒱
    (fun i j ↦ Spec (CommRingCat.of (HomogeneousLocalization.Away SG (z (i, j)))))
    (fun i j ↦ Proj.awayι SG (z (i, j))
      (segreCoordinate_denominator_mem a b i j) (by decide))
    (fun i j ↦ Spec.map (CommRingCat.ofHom (segreColumnChartMap a b G i j ha hsA).toRingHom))
    (fun i j ↦ Spec.map (CommRingCat.ofHom (segreRowChartMap a b G H i j ha hb hsB).toRingHom))
    ?_ ?_ ?_ ?_
  · intro i j
    exact segreLeftProjection_awayι a b G ha hsA i j
  · intro i j
    exact segreRightProjection_awayι a b G ha H hb hsB i j
  · change ∀ i : ι, ∀ j : κ,
      (Proj.awayι SG (z (i, j)) (segreCoordinate_denominator_mem a b i j) (by decide)).opensRange =
        (segreLeftProjection a b G ha hsA ⁻¹ᵁ
          (Proj.awayι G (a i) (ha i) (by decide)).opensRange) ⊓
        (segreRightProjection a b G ha H hb hsB ⁻¹ᵁ
          (Proj.awayι H (b j) (hb j) (by decide)).opensRange)
    intro i j
    rw [Proj.opensRange_awayι, Proj.opensRange_awayι, Proj.opensRange_awayι]
    exact (segreProjection_preimage_pair a b G ha H hb hsA hsB i j).symm
  · change ∀ i : ι, ∀ j : κ, IsPullback
      (Spec.map (CommRingCat.ofHom (segreColumnChartMap a b G i j ha hsA).toRingHom))
      (Spec.map (CommRingCat.ofHom (segreRowChartMap a b G H i j ha hb hsB).toRingHom))
      (Proj.awayι G (a i) (ha i) (by decide) ≫ projectiveCechStructureMap G)
      (Proj.awayι H (b j) (hb j) (by decide) ≫ projectiveCechStructureMap H)
    intro i j
    rw [projectiveAway_structureMap, projectiveAway_structureMap]
    exact isPullback_segreStandardOpen a b G H ha hb hsA hsB i j

end SerrePositivity.AlgebraicGeometry
