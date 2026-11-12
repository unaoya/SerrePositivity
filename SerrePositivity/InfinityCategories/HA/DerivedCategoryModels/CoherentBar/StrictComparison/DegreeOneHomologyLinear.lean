module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DegreeOneCyclesMap

/-!
概要：次数一ホモロジー射は指定次数の実成分の有限整数線形結合を保つ。
方針：cycle 上の写像の線形性を核包含で判定し、ホモロジーの全射へ送る。
規約：各作用素の閉性を保持する。
使われ方：一次列の面和と通常の bar 微分の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] {K L : Complex R}

lemma dgDegreeOneHomologyMap_linearCombination {A : Type w} [Fintype A]
    (z : Cochain K L 1) (hz : δ 1 2 z = 0)
    (c : A → ℤ) (a : A → Cochain K L 1) (ha : ∀ i, δ 1 2 (a i) = 0) (q : ℤ)
    (h : z.v q (q + 1) rfl = ∑ i, c i • (a i).v q (q + 1) rfl) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap R z hz q = ∑ i, c i • _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap R (a i) (ha i) q := by
  have hc : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneCyclesMap R z hz q =
      ∑ i, c i • _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneCyclesMap R (a i) (ha i) q := by
    rw [← cancel_mono (L.iCycles (q + 1)), Preadditive.sum_comp, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneCyclesMap_i,
      h, Preadditive.comp_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneCyclesMap_i]
  rw [← cancel_epi (K.homologyπ q), Preadditive.comp_sum, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap_cycles]
  simp only [Preadditive.comp_zsmul, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap_cycles]
  rw [hc, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
