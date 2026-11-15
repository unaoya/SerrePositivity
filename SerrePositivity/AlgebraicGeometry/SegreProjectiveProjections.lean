module

public import SerrePositivity.AlgebraicGeometry.SegreChartCompatibility
public import SerrePositivity.AlgebraicGeometry.SegreCoordinateStandardOpen
public import Mathlib.AlgebraicGeometry.Gluing

/-!
概要：Segre 座標環の Proj から、二つの因子の Proj への実際の射。
方針：標準開の交叉での可換性を、既存の開被覆の貼り合わせへ渡す。
規約：平坦性・Noether 性を仮定せず、元の次数一の全射表示を使う。
使われ方：Segre の Proj と実際のファイバー積との比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {R A B : Type u} {ι κ : Type} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] (a : ι → A) (b : κ → B)
variable (G : ℕ → Submodule R A) [GradedRing G] (ha : ∀ k, a k ∈ G 1)
local notation "SG" => segreCoordinateGrade (R := R) a b
local notation "z" => (fun p : ι × κ ↦ segreCoordinateProjection (R := R) a b (MvPolynomial.X p))
local instance segreProjectionColumnAlgebra (x : A) :
    Algebra R (HomogeneousLocalization.Away G x) := projectiveHomogeneousAwayAlgebra G x
local instance segreProjectionStandardAlgebra [GradedRing SG]
    (x : SegreCoordinateRing (R := R) a b) :
    Algebra R (HomogeneousLocalization.Away SG x) := projectiveHomogeneousAwayAlgebra SG x

/-- 実際の次数一の Segre 座標による標準開被覆。 -/
def segreProjectiveOpenCover :
    letI := segreCoordinateGradedRing a b G ha
    (Proj SG).AffineOpenCover := by
  letI := segreCoordinateGradedRing a b G ha
  exact Proj.affineOpenCoverOfIrrelevantLESpan SG z
    (fun p ↦ segreCoordinate_denominator_mem a b p.1 p.2) (fun _ ↦ by decide)
    (segreCoordinate_irrelevant_le_span a b G ha)

set_option backward.isDefEq.respectTransparency false in
/-- 実際の交叉上の可換性を、Segre の標準開被覆の貼り合わせへ渡す。 -/
def segreGlueMorphisms {Y : Scheme.{u}} :
    letI := segreCoordinateGradedRing a b G ha
    (F : ∀ p : ι × κ, Spec (CommRingCat.of (HomogeneousLocalization.Away SG (z p))) ⟶ Y) →
    (∀ p q : ι × κ,
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap SG
        (segreCoordinate_denominator_mem a b q.1 q.2) (rfl : z p * z q = z p * z q))) ≫ F p =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap SG
        (segreCoordinate_denominator_mem a b p.1 p.2) (mul_comm (z p) (z q)))) ≫ F q) →
    (Proj SG ⟶ Y) := by
  letI := segreCoordinateGradedRing a b G ha
  intro F hF
  refine (segreProjectiveOpenCover a b G ha).openCover.glueMorphisms F ?_
  change ∀ p q : ι × κ,
    pullback.fst
      (Proj.awayι SG (z p) (segreCoordinate_denominator_mem a b p.1 p.2) (by decide))
      (Proj.awayι SG (z q) (segreCoordinate_denominator_mem a b q.1 q.2) (by decide)) ≫ F p =
      pullback.snd _ _ ≫ F q
  intro p q
  change pullback.fst (Proj.awayι SG (z p) _ _) (Proj.awayι SG (z q) _ _) ≫ F p =
    pullback.snd _ _ ≫ F q
  apply (cancel_epi (Proj.pullbackAwayιIso SG
    (segreCoordinate_denominator_mem a b p.1 p.2) (by decide)
    (segreCoordinate_denominator_mem a b q.1 q.2) (by decide)
    (rfl : z p * z q = z p * z q)).inv).mp
  rw [← Category.assoc, Proj.pullbackAwayιIso_inv_fst,
    ← Category.assoc, Proj.pullbackAwayιIso_inv_snd]
  exact hF p q

/-- 列の局所射を貼り合わせた、最初の因子への実際の射。 -/
def segreLeftProjection (hsA : Function.Surjective (MvPolynomial.aeval (R := R) a)) :
    letI := segreCoordinateGradedRing a b G ha
    Proj SG ⟶ Proj G := by
  letI := segreCoordinateGradedRing a b G ha
  refine segreGlueMorphisms a b G ha (fun p ↦
    Spec.map (CommRingCat.ofHom (segreColumnChartMap a b G p.1 p.2 ha hsA).toRingHom) ≫
      Proj.awayι G (a p.1) (ha p.1) (by decide)) ?_
  intro p q
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  exact segreColumnChart_compat a b G ha p.1 q.1 p.2 q.2 hsA

/-- 最初の大域射の標準開への制限は、構成した列の局所射。 -/
theorem segreLeftProjection_awayι
    (hsA : Function.Surjective (MvPolynomial.aeval (R := R) a)) (i : ι) (j : κ) :
    letI := segreCoordinateGradedRing a b G ha
    Proj.awayι SG (z (i, j)) (segreCoordinate_denominator_mem a b i j) (by decide) ≫
      segreLeftProjection a b G ha hsA =
      Spec.map (CommRingCat.ofHom (segreColumnChartMap a b G i j ha hsA).toRingHom) ≫
        Proj.awayι G (a i) (ha i) (by decide) := by
  let := segreCoordinateGradedRing a b G ha
  unfold segreLeftProjection segreGlueMorphisms
  exact (segreProjectiveOpenCover a b G ha).openCover.ι_glueMorphisms _ _ (i, j)

variable (H : ℕ → Submodule R B) [GradedRing H] (hb : ∀ l, b l ∈ H 1)
local instance segreProjectionRowAlgebra (x : B) :
    Algebra R (HomogeneousLocalization.Away H x) := projectiveHomogeneousAwayAlgebra H x

/-- 行の局所射を貼り合わせた、二番目の因子への実際の射。 -/
def segreRightProjection (hsB : Function.Surjective (MvPolynomial.aeval (R := R) b)) :
    letI := segreCoordinateGradedRing a b G ha
    Proj SG ⟶ Proj H := by
  letI := segreCoordinateGradedRing a b G ha
  refine segreGlueMorphisms a b G ha (fun p ↦
    Spec.map (CommRingCat.ofHom (segreRowChartMap a b G H p.1 p.2 ha hb hsB).toRingHom) ≫
      Proj.awayι H (b p.2) (hb p.2) (by decide)) ?_
  intro p q
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  exact segreRowChart_compat a b G H ha hb p.1 q.1 p.2 q.2 hsB

/-- 二番目の大域射の標準開への制限は、構成した行の局所射。 -/
theorem segreRightProjection_awayι
    (hsB : Function.Surjective (MvPolynomial.aeval (R := R) b)) (i : ι) (j : κ) :
    letI := segreCoordinateGradedRing a b G ha
    Proj.awayι SG (z (i, j)) (segreCoordinate_denominator_mem a b i j) (by decide) ≫
      segreRightProjection a b G ha H hb hsB =
      Spec.map (CommRingCat.ofHom (segreRowChartMap a b G H i j ha hb hsB).toRingHom) ≫
        Proj.awayι H (b j) (hb j) (by decide) := by
  let := segreCoordinateGradedRing a b G ha
  unfold segreRightProjection segreGlueMorphisms
  exact (segreProjectiveOpenCover a b G ha).openCover.ι_glueMorphisms _ _ (i, j)

end SerrePositivity.AlgebraicGeometry
