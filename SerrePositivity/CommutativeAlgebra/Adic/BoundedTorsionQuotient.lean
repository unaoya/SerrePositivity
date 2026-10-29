module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedTorsionComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalQuotientComplete

/-! # 有界ねじれを持つ主イデアル商の完備性

概要：有界な冪ねじれを持つ完備な環を、主イデアルやその冪、自然数の像で割った商が古典的に完備であること。
方針：導来完備化との比較（HomologicalAlgebra の `DerivedCompletion`）を経由する。
規約：導来完備化に依存するので、循環を避けて `Adic/BoundedTorsion` とは別のファイルに置く。
使われ方：Bhatt–Scholze 側の Witt ベクトルと perfectoid 環。
-/

@[expose] public noncomputable section

universe u v w

namespace SerrePositivity

section AdicBoundedTorsionQuotient

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

/-- 全ての正冪商へ、与えられた有界指数で適用できる。零冪商も含む。 -/
theorem isAdicComplete_principal_power_quotient_natCast_of_bounded_torsion
    (p : ℕ) (d : R) (k : ℕ) [IsAdicComplete (Ideal.span {(p : R)}) R]
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ x : R ⧸ Ideal.span {d ^ k},
      (p : R ⧸ Ideal.span {d ^ k}) ^ n * x = 0 →
      (p : R ⧸ Ideal.span {d ^ k}) ^ N * x = 0) :
    IsAdicComplete (Ideal.span {(p : R ⧸ Ideal.span {d ^ k})}) (R ⧸ Ideal.span {d ^ k}) :=
  isAdicComplete_principal_quotient_natCast_of_bounded_torsion R p (d ^ k) hbounded

end AdicBoundedTorsionQuotient

end SerrePositivity
