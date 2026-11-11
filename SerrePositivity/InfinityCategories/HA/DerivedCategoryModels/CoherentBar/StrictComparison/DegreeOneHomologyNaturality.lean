module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DegreeOneCyclesMap

/-!
概要：次数一ホモロジー射の実鎖写像に対する前後の自然性。
方針：cycle 上の成分比較をホモロジーの全射へ送る。
規約：指定次数の中央成分の一致だけを使う。
使われ方：実直和包含と一次層作用素の係数比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R]

lemma dgDegreeOneHomologyMap_pre {K K' L : Complex R} (f : K' ⟶ K)
    (z : Cochain K L 1) (hz : δ 1 2 z = 0)
    (z' : Cochain K' L 1) (hz' : δ 1 2 z' = 0) (q : ℤ)
    (h : z'.v q (q + 1) rfl = f.f q ≫ z.v q (q + 1) rfl) :
    HomologicalComplex.homologyMap f q ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap R z hz q =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap R z' hz' q := by
  have hc : HomologicalComplex.cyclesMap f q ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneCyclesMap R z hz q =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneCyclesMap R z' hz' q := by
    rw [← cancel_mono (L.iCycles (q + 1)), Category.assoc,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneCyclesMap_i, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneCyclesMap_i, ← Category.assoc,
      HomologicalComplex.cyclesMap_i, Category.assoc, h]
  rw [← cancel_epi (K'.homologyπ q), ← Category.assoc,
    HomologicalComplex.homologyπ_naturality, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap_cycles, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap_cycles, ← Category.assoc, hc]

lemma dgDegreeOneHomologyMap_post {K L L' : Complex R} (g : L ⟶ L')
    (z : Cochain K L 1) (hz : δ 1 2 z = 0)
    (z' : Cochain K L' 1) (hz' : δ 1 2 z' = 0) (q : ℤ)
    (h : z'.v q (q + 1) rfl = z.v q (q + 1) rfl ≫ g.f (q + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap R z hz q ≫ HomologicalComplex.homologyMap g (q + 1) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap R z' hz' q := by
  have hc : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneCyclesMap R z hz q ≫ HomologicalComplex.cyclesMap g (q + 1) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneCyclesMap R z' hz' q := by
    rw [← cancel_mono (L'.iCycles (q + 1)), Category.assoc,
      HomologicalComplex.cyclesMap_i, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneCyclesMap_i, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneCyclesMap_i, Category.assoc, h]
  rw [← cancel_epi (K.homologyπ q), ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap_cycles,
    Category.assoc, HomologicalComplex.homologyπ_naturality,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap_cycles, ← Category.assoc, hc]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
