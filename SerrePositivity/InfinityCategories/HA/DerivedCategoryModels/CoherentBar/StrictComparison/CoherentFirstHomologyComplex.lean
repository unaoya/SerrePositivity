module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerShortExact
public import Mathlib.Algebra.Homology.HomologySequence

/-!
概要：実 coherent bar の単体次元フィルトレーションの一次ホモロジー複体。
方針：隣接段階の短完全列の連結射を、次の次元層へ射影する。
規約：二乗零は実短完全列の長完全列から導き、高次 HA 成分を零としない。
使われ方：通常の非退化ホモロジー bar との微分の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

abbrev dgCoherentBarFirstHomologyObject (x : D) (r : ℤ) (n : ℕ) : ModuleCat R :=
  ((moduleEvaluation R D x).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G n)).homology (r - (n : ℤ))

def dgCoherentBarFirstHomologyDifferential (x : D) (r : ℤ) (n : ℕ) :
    dgCoherentBarFirstHomologyObject R D G x r (n + 1) ⟶
      dgCoherentBarFirstHomologyObject R D G x r n :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerSequence_shortExact R D G x n).δ
    (r - ((n + 1 : ℕ) : ℤ)) (r - (n : ℤ))
    (by change r - ((n + 1 : ℕ) : ℤ) + 1 = r - (n : ℤ); omega) ≫
    HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageToLayer R D G x n) (r - (n : ℤ))

lemma dgCoherentBarFirstHomologyDifferential_sq (x : D) (r : ℤ) (n : ℕ) :
    dgCoherentBarFirstHomologyDifferential R D G x r (n + 1) ≫
      dgCoherentBarFirstHomologyDifferential R D G x r n = 0 := by
  unfold dgCoherentBarFirstHomologyDifferential
  rw [Category.assoc, ← Category.assoc
    (HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageToLayer R D G x (n + 1)) _)]
  erw [(_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerSequence_shortExact R D G x n).comp_δ
    (r - ((n + 1 : ℕ) : ℤ)) (r - (n : ℤ))
    (by change r - ((n + 1 : ℕ) : ℤ) + 1 = r - (n : ℤ); omega)]
  simp only [zero_comp, comp_zero]

def dgCoherentBarFirstHomologyComplex (x : D) (r : ℤ) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (dgCoherentBarFirstHomologyObject R D G x r)
    (dgCoherentBarFirstHomologyDifferential R D G x r)
    (dgCoherentBarFirstHomologyDifferential_sq R D G x r)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
