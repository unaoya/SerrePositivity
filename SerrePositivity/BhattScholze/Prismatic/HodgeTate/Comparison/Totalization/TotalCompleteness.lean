module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.ExtensionFunctor
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.LowerBound
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Localization

/-!
# 完備な行からなる積全複体の完備性

## 概要
元の各行が主元について導来完備なら、指定された積全複体も導来完備である。

## 方針
局所化の既存の自由分解からの Hom で完備性を判定し、Hom–Tot 同型と対角線の完全性を使う。

## 規約
完備性は本体の IsComplete を用いる。行のコホモロジーの有界性は要求しない。

## 使われ方
BS 著者版 Lemma 4.22 の比較の標的となる、完備化後の行の Tot。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal

attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- 各行の導来完備性は、指定された積全複体へ渡る。 -/
theorem total_isComplete (a : R) (K : CochainComplex (Complex R) ℕ)
    (hK : ∀ n : ℕ, IsComplete R a (DerivedCategory.Q.obj (K.X n))) :
    IsComplete R a (DerivedCategory.Q.obj (total K)) := by
  apply (isComplete_iff_localizationResolutionHom_acyclic R a (total K)).mpr
  rw [acyclic_iff]
  intro i
  rw [exactAt_iff_isZero_homology]
  let P := localizationResolutionComplex R a
  let H := ((homFunctor P).mapHomologicalComplex (.up ℕ)).obj K
  have hz : IsZero ((total H).homology i) := by
    apply total_homology_isZero_of_diagonal
    intro n
    have hn := (isComplete_iff_localizationResolutionHom_acyclic R a (K.X n)).mp (hK n)
    rw [acyclic_iff] at hn
    exact (exactAt_iff_isZero_homology _ _).mp (hn (i - n))
  exact hz.of_iso ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso (homTotalIsoNat P K))

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
