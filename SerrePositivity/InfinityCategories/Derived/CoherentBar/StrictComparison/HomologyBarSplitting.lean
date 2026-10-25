module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarSplittingCoefficients
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.WeightedCoproductDecomposition
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarFilteredExact
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarZeroHomology
public import Mathlib.AlgebraicTopology.DoldKan.SplitSimplicialObject

/-!
概要：通常のホモロジー bar の canonical splitting と非退化複体。
方針：係数つき直和分解を splitting にし、既存の Dold–Kan ホモトピー同値を使う。
規約：ここで正規化するのは H(G) の通常の bar であり、G 自体を strict 化しない。
使われ方：実 bar の各層の内部ホモロジーに現れる非退化 bar の完全性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits Opposite SSet AlgebraicTopology HomologicalComplex
open scoped Simplicial
variable (R : Type u) [CommRing R] {J : Type u} [PartialOrder J]
  (F : J ⥤ ModuleCat.{u} R)

def dgHomologyBarSplitting : (dgHomologyBarSimplicial R F).Splitting where
  N := dgHomologyBarNondegGraded R F
  ι := dgHomologyBarNondegInclusion R F
  isColimit' Δ := by
    have h := dgBarCoproductDecompositionIsColimit R
      (dgHomologyBarFamily R F Δ)
      (fun A : SimplicialObject.Splitting.IndexSet Δ => dgHomologyBarNondegFamily R F A.1.unop.len)
      (dgHomologyBarSplittingIndexEquiv (J := J) Δ)
      (dgHomologyBarSplittingCoefficientIso R F Δ)
    simpa only [dgBarCoproductDecompositionCofan, SimplicialObject.Splitting.cofan',
      dgHomologyBarSplitting_leg] using! h

abbrev dgHomologyBarNondegComplex : ChainComplex (ModuleCat R) ℕ :=
  (dgHomologyBarSplitting R F).nondegComplex

def dgHomologyBarNondegHomotopyEquiv :
    HomotopyEquiv (dgHomologyBarComplex R F) (dgHomologyBarNondegComplex R F) :=
  (dgHomologyBarSplitting R F).homotopyEquivNondegComplex

def dgHomologyBarNondegZeroHomologyIso :
    (dgHomologyBarNondegComplex R F).homology 0 ≅ colimit F :=
  ((dgHomologyBarNondegHomotopyEquiv R F).toHomologyIso 0).symm ≪≫
    dgHomologyBarZeroHomologyColimitIso R F

lemma dgHomologyBarNondeg_exactAt [IsFiltered J] (n : ℕ) :
    (dgHomologyBarNondegComplex R F).ExactAt (n + 1) := by
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
  have h := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (dgHomologyBarFiltered_exactAt R F n)
  exact h.of_iso ((dgHomologyBarNondegHomotopyEquiv R F).toHomologyIso (n + 1)).symm

end SerrePositivity.InfinityCategories
