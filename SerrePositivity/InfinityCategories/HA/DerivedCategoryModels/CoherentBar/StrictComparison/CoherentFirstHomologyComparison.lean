module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstHomologyDifferential
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstLayerConnecting

/-!
概要：実フィルトレーションの一次ホモロジー複体と非退化 H(G) bar の同型。
方針：実連結射と一次層作用素の比較を、総次数を固定した層同型へ合わせる。
規約：元の coherent 図式の高次成分を保持した実フィルトレーションを使う。
使われ方：全正単体次元の完全性と有限 support による収束。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet HomologicalComplex
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarConnectingHomology_comparison (x : D) (n : ℕ) (p t r : ℤ)
    (hpt : p + 1 = t) (hs : ((n + 1 : ℕ) : ℤ) + p = r) (ht : (n : ℤ) + t = r) :
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerSequence_shortExact R D G x n).δ p t
        (by change p + 1 = t; exact hpt) ≫
      HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageToLayer R D G x n) t) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNaturalLayerHomologyIso R D G x n t r ht).hom =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNaturalLayerHomologyIso R D G x (n + 1) p r hs).hom ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegComplex R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x r)).d (n + 1) n := by
  subst t
  erw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerConnecting_eq_firstHomology]
  have hr : p + ((n : ℤ) + 1) = r := by omega
  obtain rfl : r = p + ((n : ℤ) + 1) := hr.symm
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFirstLayerHomology_differential R D G x p n

def dgCoherentBarFirstHomologyComparison (x : D) (r : ℤ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFirstHomologyComplex R D G x r ≅
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegComplex R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x r) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNaturalLayerHomologyIso R D G x n (r - (n : ℤ)) r (by omega))
    (fun i j hij => by
      change j + 1 = i at hij
      subst i
      dsimp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFirstHomologyComplex]
      rw [ChainComplex.of_d]
      symm
      dsimp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFirstHomologyDifferential]
      exact dgCoherentBarConnectingHomology_comparison R D G x j
        (r - ((j + 1 : ℕ) : ℤ)) (r - (j : ℤ)) r (by omega) (by omega) (by omega))

lemma dgCoherentBarFirstHomology_exactAt [IsFiltered J] (x : D) (r : ℤ) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFirstHomologyComplex R D G x r).ExactAt (n + 1) := by
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
  have h := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondeg_exactAt R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x r) n)
  exact h.of_iso (HomologicalComplex.homologyMapIso (dgCoherentBarFirstHomologyComparison R D G x r) (n + 1))

def dgCoherentBarFirstHomologyZeroIso (x : D) (r : ℤ) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFirstHomologyComplex R D G x r).homology 0 ≅
      colimit (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x r) :=
  HomologicalComplex.homologyMapIso (dgCoherentBarFirstHomologyComparison R D G x r) 0 ≪≫
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegZeroHomologyIso R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x r)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
