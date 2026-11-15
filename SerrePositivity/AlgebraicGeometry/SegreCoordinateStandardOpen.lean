module

public import SerrePositivity.AlgebraicGeometry.SegreCoordinateRing
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
概要：実際の Segre 座標環の有限な標準開条件と射影 Čech 入力の同時供給。
方針：商の次数成分の原像を使い、斉次多項式の次数と生成イデアルの冪の法則を適用する。
規約：標準開条件を仮定にしない。空の添字・零環も許す。
使われ方：G3 の Segre 表示と 2f の射影 Čech の入力の接続。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
universe u
variable {R A B : Type u} {ι κ : Type} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] (a : ι → A) (b : κ → B)

/-- 同じ商写像は、変数の像による実際の評価と等しい。 -/
theorem segreCoordinate_aeval :
    MvPolynomial.aeval (R := R) (fun ij : ι × κ ↦
      segreCoordinateProjection (R := R) a b (MvPolynomial.X ij)) =
        segreCoordinateProjection (R := R) a b := by
  ext ij
  simp

variable (G : ℕ → Submodule R A) [GradedRing G] (ha : ∀ i, a i ∈ G 1)

/-- 実際の Segre 座標の変数の像は irrelevant ideal を生成する。 -/
theorem segreCoordinate_irrelevant_le_span :
    letI := segreCoordinateGradedRing a b G ha
    (HomogeneousIdeal.irrelevant (segreCoordinateGrade (R := R) a b)).toIdeal ≤
      Ideal.span (Set.range (fun ij : ι × κ ↦
        segreCoordinateProjection (R := R) a b (MvPolynomial.X ij))) := by
  letI := segreCoordinateGradedRing a b G ha
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro d hd x hx
  obtain ⟨f, hf, rfl⟩ := hx
  apply Ideal.pow_le_self (Nat.ne_of_gt hd)
  rw [Ideal.mem_span_pow_iff_exists_isHomogeneous]
  refine ⟨MvPolynomial.map (algebraMap R (SegreCoordinateRing (R := R) a b)) f,
    ((MvPolynomial.mem_homogeneousSubmodule d f).mp hf).map _, ?_⟩
  rw [MvPolynomial.eval_map]
  change MvPolynomial.aeval (R := R) (fun ij : ι × κ ↦
      segreCoordinateProjection (R := R) a b (MvPolynomial.X ij)) f =
        segreCoordinateProjection (R := R) a b f
  rw [segreCoordinate_aeval]

/-- 同じ変数の像の標準開は実際の Segre 座標環の Proj を被覆する。 -/
theorem iSup_segreCoordinate_basicOpen :
    letI := segreCoordinateGradedRing a b G ha
    ⨆ ij : ι × κ, Proj.basicOpen (segreCoordinateGrade (R := R) a b)
      (segreCoordinateProjection (R := R) a b (MvPolynomial.X ij)) = ⊤ := by
  letI := segreCoordinateGradedRing a b G ha
  exact Proj.iSup_basicOpen_eq_top _ _ (segreCoordinate_irrelevant_le_span a b G ha)

/-- 同じ商と次数分解は 2f の射影 Čech 計算の入力を同時に持つ。 -/
theorem segreCoordinate_projective_cech_data [Fintype ι] [Fintype κ] :
    letI := segreCoordinateGradedRing a b G ha
    IsScalarTower R (MvPolynomial (ι × κ) R) (SegreCoordinateRing (R := R) a b) ∧
      SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (ι × κ) R)
        (segreCoordinateGrade (R := R) a b) ∧
      Module.Finite (MvPolynomial (ι × κ) R) (SegreCoordinateRing (R := R) a b) ∧
      (HomogeneousIdeal.irrelevant (segreCoordinateGrade (R := R) a b)).toIdeal ≤
        Ideal.span (Set.range (fun ij : ι × κ ↦
          algebraMap (MvPolynomial (ι × κ) R) (SegreCoordinateRing (R := R) a b)
            (MvPolynomial.X ij))) := by
  letI := segreCoordinateGradedRing a b G ha
  exact ⟨inferInstance, segreCoordinateGradedSMul (R := R) a b,
    segreCoordinateRing_finite (R := R) a b, segreCoordinate_irrelevant_le_span a b G ha⟩

end SerrePositivity.AlgebraicGeometry
