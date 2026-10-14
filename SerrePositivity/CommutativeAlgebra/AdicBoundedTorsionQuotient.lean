module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedTorsionComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalQuotientComplete

/-! # 有界冪ねじれを持つ主イデアル商の古典的完備性

BS共通要求F5。共通定理は素数性・生成元の正則性・Noether性を要しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- f進完備環の主イデアル商が有界f冪ねじれを持てば、商は古典的完備。 -/
theorem isAdicComplete_principal_quotient_of_bounded_torsion (f d : R)
    [IsAdicComplete (Ideal.span {f}) R]
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : R ⧸ Ideal.span {d},
      (Ideal.Quotient.mk (Ideal.span {d}) f) ^ n * x = 0 →
      (Ideal.Quotient.mk (Ideal.span {d}) f) ^ N * x = 0) :
    IsAdicComplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {d}) f})
      (R ⧸ Ideal.span {d}) := by
  have hR := DerivedCompletion.isModuleComplete_of_isAdicComplete R f (ModuleCat.of R R)
  exact DerivedCompletion.isAdicComplete_of_isModuleComplete_of_bounded_torsion
    (R ⧸ Ideal.span {d}) (Ideal.Quotient.mk (Ideal.span {d}) f)
    (ModuleCat.of (R ⧸ Ideal.span {d}) (R ⧸ Ideal.span {d}))
    (DerivedCompletion.isModuleComplete_principal_quotient R f d hR) hbounded

/-- 自然数pの像を用いるF5の一般形。p正則性とd正則性は不要。 -/
theorem isAdicComplete_principal_quotient_natCast_of_bounded_torsion (p : ℕ) (d : R)
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : R ⧸ Ideal.span {d},
      (p : R ⧸ Ideal.span {d}) ^ n * x = 0 →
      (p : R ⧸ Ideal.span {d}) ^ N * x = 0) :
    IsAdicComplete (Ideal.span {(p : R ⧸ Ideal.span {d})}) (R ⧸ Ideal.span {d}) := by
  simpa only [map_natCast] using
    isAdicComplete_principal_quotient_of_bounded_torsion R (p : R) d hbounded

/-- BS要求の正確な直接形。要求の正則性は一般定理からの適用では不要。 -/
theorem isAdicComplete_regular_quotient_natCast_of_bounded_torsion (p : ℕ) [Fact p.Prime]
    (d : R) [IsAdicComplete (Ideal.span {(p : R)}) R]
    (_hp : Function.Injective (fun x : R ↦ (p : R) * x))
    (_hd : Function.Injective (fun x : R ↦ d * x))
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : R ⧸ Ideal.span {d},
      (p : R ⧸ Ideal.span {d}) ^ n * x = 0 →
      (p : R ⧸ Ideal.span {d}) ^ N * x = 0) :
    IsAdicComplete (Ideal.span {(p : R ⧸ Ideal.span {d})}) (R ⧸ Ideal.span {d}) :=
  isAdicComplete_principal_quotient_natCast_of_bounded_torsion R p d hbounded

/-- 全ての正冪商へ、与えられた有界指数で適用できる。零冪商も含む。 -/
theorem isAdicComplete_principal_power_quotient_natCast_of_bounded_torsion
    (p : ℕ) (d : R) (k : ℕ) [IsAdicComplete (Ideal.span {(p : R)}) R]
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : R ⧸ Ideal.span {d ^ k},
      (p : R ⧸ Ideal.span {d ^ k}) ^ n * x = 0 →
      (p : R ⧸ Ideal.span {d ^ k}) ^ N * x = 0) :
    IsAdicComplete (Ideal.span {(p : R ⧸ Ideal.span {d ^ k})}) (R ⧸ Ideal.span {d ^ k}) :=
  isAdicComplete_principal_quotient_natCast_of_bounded_torsion R p (d ^ k) hbounded

end SerrePositivity
