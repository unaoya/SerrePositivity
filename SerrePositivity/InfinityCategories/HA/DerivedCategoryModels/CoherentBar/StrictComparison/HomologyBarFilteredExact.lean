module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarLowerCover

/-!
概要：filtered poset 上の通常のホモロジー bar は正次数で完全である。
方針：有限 cycle を終頂点のある下方部分圏へ持ち上げ、局所縮約の boundary を写す。
規約：元の G の strict 性は使わない。ここでの F は H(G) である。
使われ方：単体次元フィルトレーションでの正次数の消滅。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits Opposite SSet AlgebraicTopology HomologicalComplex
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] {J : Type u} [PartialOrder J] [IsFiltered J]
  (F : J ⥤ ModuleCat.{u} R)

lemma dgHomologyBarFiltered_cycle_boundary (n : ℕ)
    (z : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarComplex R F).X (n + 1))
    (hz : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarComplex R F).d (n + 1) n z = 0) :
    ∃ a : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarComplex R F).X (n + 2),
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarComplex R F).d (n + 2) (n + 1) a = z := by
  obtain ⟨b, a, ha⟩ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerMap_covers R F (n + 1) z
  have hz' : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarComplex R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerDiagram R F b)).d (n + 1) n a = 0 := by
    apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerMap_injective R F b n
    rw [map_zero]
    have h := ConcreteCategory.congr_hom ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerMap R F b).comm (n + 1) n) a
    change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarComplex R F).d (n + 1) n
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerMap R F b).f (n + 1) a) =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerMap R F b).f n
        ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarComplex R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerDiagram R F b)).d (n + 1) n a) at h
    rw [ha, hz] at h
    exact h.symm
  obtain ⟨w, hw⟩ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarTop_cycle_boundary R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerDiagram R F b) n a hz'
  refine ⟨(_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerMap R F b).f (n + 2) w, ?_⟩
  have h := ConcreteCategory.congr_hom ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerMap R F b).comm (n + 2) (n + 1)) w
  change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarComplex R F).d (n + 2) (n + 1)
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerMap R F b).f (n + 2) w) =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerMap R F b).f (n + 1)
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarComplex R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerDiagram R F b)).d (n + 2) (n + 1) w) at h
  exact h.trans ((congrArg ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarLowerMap R F b).f (n + 1)) hw).trans ha)

lemma dgHomologyBarFiltered_exactAt (n : ℕ) : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarComplex R F).ExactAt (n + 1) := by
  apply (HomologicalComplex.exactAt_iff' (K := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarComplex R F)
    (i := n + 2) (j := n + 1) (k := n) (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  exact dgHomologyBarFiltered_cycle_boundary R F n

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
