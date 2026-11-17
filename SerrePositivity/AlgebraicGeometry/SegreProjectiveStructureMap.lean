module

public import SerrePositivity.AlgebraicGeometry.SegreProjectiveProjections

/-!
概要：Segre の二つの大域射は、元の Spec R 上の構造射を保つ。
方針：全標準開に制限し、列・行の代数写像が R 上であることを使う。
規約：別の構造射へ置き換えず、元のスカラー写像を保つ。
使われ方：有限ファイバー冪の次数一表示を同じ基底上で帰納する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
variable {R A B : Type u} {ι κ : Type} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] (a : ι → A) (b : κ → B)
variable (G : ℕ → Submodule R A) [GradedRing G] (ha : ∀ k, a k ∈ G 1)
local notation "SG" => segreCoordinateGrade (R := R) a b
local notation "z" => (fun p : ι × κ ↦ segreCoordinateProjection (R := R) a b (MvPolynomial.X p))
local instance segreStructureColumnAlgebra (x : A) :
    Algebra R (HomogeneousLocalization.Away G x) := projectiveHomogeneousAwayAlgebra G x
local instance segreStructureStandardAlgebra [GradedRing SG]
    (x : SegreCoordinateRing (R := R) a b) :
    Algebra R (HomogeneousLocalization.Away SG x) := projectiveHomogeneousAwayAlgebra SG x

set_option backward.isDefEq.respectTransparency false in
/-- 最初の Segre 射影は、元のスカラー構造射を保つ。 -/
theorem segreLeftProjection_structureMap
    (hsA : Function.Surjective (MvPolynomial.aeval (R := R) a)) :
    letI := segreCoordinateGradedRing a b G ha
    segreLeftProjection a b G ha hsA ≫ projectiveCechStructureMap G =
      projectiveCechStructureMap SG := by
  let := segreCoordinateGradedRing a b G ha
  apply (segreProjectiveOpenCover a b G ha).openCover.hom_ext
  change ∀ p : ι × κ,
    Proj.awayι SG (z p) (segreCoordinate_denominator_mem a b p.1 p.2) (by decide) ≫
      (segreLeftProjection a b G ha hsA ≫ projectiveCechStructureMap G) =
    Proj.awayι SG (z p) (segreCoordinate_denominator_mem a b p.1 p.2) (by decide) ≫
      projectiveCechStructureMap SG
  rintro ⟨i, j⟩
  rw [← Category.assoc, segreLeftProjection_awayι, Category.assoc,
    projectiveAway_structureMap, projectiveAway_structureMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (segreColumnChartMap a b G i j ha hsA).commutes r

variable (H : ℕ → Submodule R B) [GradedRing H] (hb : ∀ l, b l ∈ H 1)
local instance segreStructureRowAlgebra (x : B) :
    Algebra R (HomogeneousLocalization.Away H x) := projectiveHomogeneousAwayAlgebra H x

set_option backward.isDefEq.respectTransparency false in
/-- 二番目の Segre 射影も、同じスカラー構造射を保つ。 -/
theorem segreRightProjection_structureMap
    (hsB : Function.Surjective (MvPolynomial.aeval (R := R) b)) :
    letI := segreCoordinateGradedRing a b G ha
    segreRightProjection a b G ha H hb hsB ≫ projectiveCechStructureMap H =
      projectiveCechStructureMap SG := by
  let := segreCoordinateGradedRing a b G ha
  apply (segreProjectiveOpenCover a b G ha).openCover.hom_ext
  change ∀ p : ι × κ,
    Proj.awayι SG (z p) (segreCoordinate_denominator_mem a b p.1 p.2) (by decide) ≫
      (segreRightProjection a b G ha H hb hsB ≫ projectiveCechStructureMap H) =
    Proj.awayι SG (z p) (segreCoordinate_denominator_mem a b p.1 p.2) (by decide) ≫
      projectiveCechStructureMap SG
  rintro ⟨i, j⟩
  rw [← Category.assoc, segreRightProjection_awayι, Category.assoc,
    projectiveAway_structureMap, projectiveAway_structureMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (segreRowChartMap a b G H i j ha hb hsB).commutes r

end SerrePositivity.AlgebraicGeometry
