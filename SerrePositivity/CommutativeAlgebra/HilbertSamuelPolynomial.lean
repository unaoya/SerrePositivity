module

public import SerrePositivity.CommutativeAlgebra.HilbertSerre
public import SerrePositivity.CommutativeAlgebra.HilbertSeries
public import SerrePositivity.CommutativeAlgebra.ReesPresentation

/-! # Hilbert–Serre の I 進随伴次数加群への適用

実際の Rees 加群による商を次数付き多項式加群として扱い、
Hilbert–Serre から Hilbert 級数の有理型表示を得る。
多項式性や次元定理の未証明入力は使わない。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.HilbertSamuel

open DirectSum IsLocalRing Polynomial
open scoped DirectSum

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- Rees 加群の商の中での第 n 次成分。 -/
def reesGrade (n : ℕ) : Submodule R (ReesGraded R I M) :=
  (gradedSingle R I M n).range

lemma gradedSingle_injective (n : ℕ) : Function.Injective (gradedSingle R I M n) :=
  (show Function.LeftInverse (gradedCoefficient R I M n) (gradedSingle R I M n) from
    gradedCoefficient_gradedSingle_self R I M n).injective

/-- 各次数の実際の商と、全体の中でのその像の同型。 -/
def gradedPieceRangeEquiv (n : ℕ) : GradedPiece R I M n ≃ₗ[R] reesGrade R I M n :=
  LinearEquiv.ofInjective (gradedSingle R I M n) (gradedSingle_injective R I M n)

/-- Rees 加群の商の各次数は内部直和をなす。 -/
theorem isInternal_reesGrade : DirectSum.IsInternal (reesGrade R I M) := by
  apply HilbertSerre.isInternal_of_projections (reesGrade R I M)
    (fun n => (gradedSingle R I M n).comp (gradedCoefficient R I M n))
  · intro n x
    obtain ⟨y, hy⟩ := x.2
    change gradedSingle R I M n (gradedCoefficient R I M n (x : ReesGraded R I M)) = x
    rw [← hy, gradedCoefficient_gradedSingle_self]
  · intro n k hkn x
    obtain ⟨y, hy⟩ := x.2
    change gradedSingle R I M n (gradedCoefficient R I M n (x : ReesGraded R I M)) = 0
    rw [← hy, gradedCoefficient_gradedSingle_ne R I M n k hkn, map_zero]
  · apply top_unique
    intro x hx
    clear hx
    obtain ⟨y, rfl⟩ := directSumToReesGraded_surjective R I M x
    induction y using DirectSum.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | of n y =>
      rw [← DirectSum.lof_eq_of R, directSumToReesGraded, DirectSum.toModule_lof]
      exact (le_iSup (reesGrade R I M) n) ⟨y, rfl⟩
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- 係数を元の環 R に取る多項式環の作用。 -/
@[instance_reducible]
def reesPolynomialModule {s : ℕ} (z : Fin s → R) (hz : Ideal.span (Set.range z) = I) :
    Module (MvPolynomial (Fin s) R) (ReesGraded R I M) :=
  Module.compHom _ (reesPresentation R I z hz).toRingHom

lemma reesPolynomialModule_scalarTower {s : ℕ} (z : Fin s → R)
    (hz : Ideal.span (Set.range z) = I) :
    let _ := reesPolynomialModule R I M z hz
    IsScalarTower R (MvPolynomial (Fin s) R) (ReesGraded R I M) := by
  let := reesPolynomialModule R I M z hz
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  change (reesPresentation R I z hz (algebraMap R (MvPolynomial (Fin s) R) r)) • x = r • x
  rw [AlgHom.commutes]
  exact algebraMap_smul (reesAlgebra I) r x

lemma reesPolynomialModule_finite [IsNoetherianRing R] [Module.Finite R M]
    {s : ℕ} (z : Fin s → R) (hz : Ideal.span (Set.range z) = I) :
    let _ := reesPolynomialModule R I M z hz
    Module.Finite (MvPolynomial (Fin s) R) (ReesGraded R I M) := by
  let : Algebra (MvPolynomial (Fin s) R) (reesAlgebra I) :=
    (reesPresentation R I z hz).toRingHom.toAlgebra
  let := reesPolynomialModule R I M z hz
  let : IsScalarTower (MvPolynomial (Fin s) R) (reesAlgebra I) (ReesGraded R I M) :=
    IsScalarTower.of_compHom (MvPolynomial (Fin s) R) (reesAlgebra I) (ReesGraded R I M)
  let : Module.Finite (MvPolynomial (Fin s) R) (reesAlgebra I) :=
    Module.Finite.of_surjective (Algebra.linearMap _ _) (reesPresentation_surjective R I z hz)
  exact Module.Finite.trans (reesAlgebra I) _

lemma reesPolynomialModule_degree_one {s : ℕ} (z : Fin s → R)
    (hz : Ideal.span (Set.range z) = I) :
    let _ := reesPolynomialModule R I M z hz
    ∀ (i : Fin s) n, ∀ x ∈ reesGrade R I M n,
      (MvPolynomial.X i : MvPolynomial (Fin s) R) • x ∈ reesGrade R I M (n + 1) := by
  let := reesPolynomialModule R I M z hz
  dsimp only
  intro i n x hx
  obtain ⟨y, rfl⟩ := hx
  let a : I := ⟨z i, hz ▸ Ideal.subset_span (Set.mem_range_self i)⟩
  have hr : reesPresentation R I z hz (MvPolynomial.X i) = reesDegreeOne R I a := by
    apply Subtype.ext
    exact reesPresentation_X R I z hz i
  change (reesPresentation R I z hz (MvPolynomial.X i)) • gradedSingle R I M n y ∈ _
  rw [hr, reesDegreeOne_smul_gradedSingle]
  exact ⟨gradedMultiplication R I M a n y, rfl⟩

/-- Rees 商の次数の長さの級数は、元の I 進 Hilbert 級数そのもの。 -/
lemma lengthSeries_reesGrade :
    HilbertSerre.lengthSeries (reesGrade R I M) = hilbertSeries R I M := by
  ext n
  simp only [HilbertSerre.lengthSeries, hilbertSeries, PowerSeries.coeff_mk,
    hilbertFunction, (gradedPieceRangeEquiv R I M n).length_eq]

/-- I 進随伴次数加群に Hilbert–Serre を適用して、有理型の Hilbert 級数を得る。 -/
theorem exists_rational_hilbertSeries [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]
    (hI : I.radical = maximalIdeal R) {s : ℕ} (z : Fin s → R)
    (hz : Ideal.span (Set.range z) = I) :
    ∃ Q : ℚ[X], hilbertSeries R I M = Q * (PowerSeries.invOneSubPow ℚ s).val := by
  let := reesPolynomialModule R I M z hz
  let : IsScalarTower R (MvPolynomial (Fin s) R) (ReesGraded R I M) :=
    reesPolynomialModule_scalarTower R I M z hz
  let : Module.Finite (MvPolynomial (Fin s) R) (ReesGraded R I M) :=
    reesPolynomialModule_finite R I M z hz
  let : Decomposition (reesGrade R I M) := (isInternal_reesGrade R I M).chooseDecomposition
  have hfinite (n : ℕ) : IsFiniteLength R (reesGrade R I M n) :=
    (isFiniteLength_gradedPiece R I M hI n).of_injective
      (f := (gradedPieceRangeEquiv R I M n).symm.toLinearMap)
      (gradedPieceRangeEquiv R I M n).symm.injective
  obtain ⟨Q, hQ⟩ := HilbertSerre.exists_rational_lengthSeries R s (ReesGraded R I M)
    (reesGrade R I M) hfinite (reesPolynomialModule_degree_one R I M z hz)
  exact ⟨Q, (lengthSeries_reesGrade R I M).symm.trans hQ⟩

end SerrePositivity.HilbertSamuel
