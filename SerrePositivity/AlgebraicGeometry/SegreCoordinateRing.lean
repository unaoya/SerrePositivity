module

public import SerrePositivity.AlgebraicGeometry.SegreGradedCoordinates
public import SerrePositivity.AlgebraicGeometry.HomogeneousIdealQuotientGrading
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
概要：実際の Segre 座標写像の核による商と、その次数分解・多項式作用を供給する。
方針：証明済みの核の斉次性を同次商の分解に適用し、有限性は実際の商写像から得る。
規約：Proj の積との比較はまだ主張しない。零環・空の添字を許す。
使われ方：G3 の標準開のテンソル比較と有限ファイバー冪の射影表示。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R A B : Type u} {ι κ : Type} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] (a : ι → A) (b : κ → B)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- 実際の Segre 座標の核による座標環。 -/
abbrev SegreCoordinateRing := MvPolynomial (ι × κ) R ⧸ RingHom.ker (segreCoordinateMap (R := R) a b).toRingHom

/-- 同じ実際の商の次数成分。 -/
def segreCoordinateGrade : ℕ → Submodule R (SegreCoordinateRing (R := R) a b) :=
  projectiveRingQuotientGrade (RingHom.ker (segreCoordinateMap (R := R) a b).toRingHom)
    (MvPolynomial.homogeneousSubmodule (ι × κ) R)

/-- 実際の多項式環から座標環への商写像。 -/
def segreCoordinateProjection : MvPolynomial (ι × κ) R →ₐ[R] SegreCoordinateRing (R := R) a b :=
  Ideal.Quotient.mkₐ R _

/-- 実際の商写像は全射。 -/
theorem segreCoordinateProjection_surjective : Function.Surjective (segreCoordinateProjection (R := R) a b) :=
  Ideal.Quotient.mk_surjective

/-- 座標環は同じ多項式環上の有限加群。 -/
theorem segreCoordinateRing_finite : Module.Finite (MvPolynomial (ι × κ) R) (SegreCoordinateRing (R := R) a b) :=
  Module.Finite.of_surjective (Algebra.linearMap _ _) Ideal.Quotient.mk_surjective

/-- 元の Noether 基底と有限の添字から、座標環の Noether 性を得る。 -/
theorem segreCoordinateRing_noetherian [IsNoetherianRing R] [Fintype ι] [Fintype κ] :
    IsNoetherianRing (SegreCoordinateRing (R := R) a b) := by
  change IsNoetherianRing (MvPolynomial (ι × κ) R ⧸ RingHom.ker (segreCoordinateMap (R := R) a b).toRingHom)
  infer_instance

/-- 商写像は既存の次数成分へ斉次元を送る。 -/
theorem segreCoordinateProjection_preservesPiece {d : ℕ} (f : MvPolynomial (ι × κ) R)
    (hf : f ∈ MvPolynomial.homogeneousSubmodule (ι × κ) R d) :
    segreCoordinateProjection (R := R) a b f ∈ segreCoordinateGrade (R := R) a b d := ⟨f, hf, rfl⟩

/-- 商の次数成分は同じ多項式環の次数付き作用を持つ。 -/
theorem segreCoordinateGradedSMul [Fintype ι] [Fintype κ] :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (ι × κ) R)
      (segreCoordinateGrade (R := R) a b) := by
  classical
  exact projectiveRingQuotientGradeGradedSMul (ι := ι × κ)
    (RingHom.ker (segreCoordinateMap (R := R) a b).toRingHom)
    (MvPolynomial.homogeneousSubmodule (ι × κ) R)

/-- 証明済みの核の斉次性から、座標環の実際の次数分解を得る。 -/
@[instance_reducible]
def segreCoordinateGradedRing (G : ℕ → Submodule R A) [GradedRing G]
    (ha : ∀ i, a i ∈ G 1) : GradedRing (segreCoordinateGrade (R := R) a b) :=
  homogeneousIdealQuotientGradedRing _ _ (segreCoordinateMap_kernel_homogeneous G a b ha)

end SerrePositivity.AlgebraicGeometry
