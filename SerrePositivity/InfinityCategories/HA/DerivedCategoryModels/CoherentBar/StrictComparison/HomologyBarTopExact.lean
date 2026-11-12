module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarTopContraction
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
概要：終頂点を持つ poset 上のホモロジー bar は正次数で完全である。
方針：検証済みの末尾付加縮約を cycle に適用し、明示的な boundary を与える。
規約：正次数のみを主張する。零次の余極限比較は別に示す。
使われ方：filtered な全体への完全性の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits Opposite SSet AlgebraicTopology HomologicalComplex
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] {J : Type u} [PartialOrder J]
  (F : J ⥤ ModuleCat.{u} R)

abbrev dgHomologyBarComplex : ChainComplex (ModuleCat R) ℕ :=
  AlternatingFaceMapComplex.obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F)

variable [OrderTop J]

lemma dgHomologyBarTop_cycle_boundary (n : ℕ)
    (z : (dgHomologyBarComplex R F).X (n + 1))
    (hz : (dgHomologyBarComplex R F).d (n + 1) n z = 0) :
    ∃ a : (dgHomologyBarComplex R F).X (n + 2),
      (dgHomologyBarComplex R F).d (n + 2) (n + 1) a = z := by
  have he := ConcreteCategory.congr_hom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarTopHomotopy_positive R F n) z
  change AlternatingFaceMapComplex.objD (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F) (n + 1)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarTopHomotopy R F (n + 1) z) +
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarTopHomotopy R F n
      (AlternatingFaceMapComplex.objD (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F) n z) = z at he
  have hz' : AlternatingFaceMapComplex.objD (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F) n z = 0 := by
    simpa only [dgHomologyBarComplex, AlternatingFaceMapComplex.obj_d_eq] using! hz
  rw [hz', map_zero, add_zero] at he
  refine ⟨_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarTopHomotopy R F (n + 1) z, ?_⟩
  simpa only [dgHomologyBarComplex, AlternatingFaceMapComplex.obj_d_eq] using! he

lemma dgHomologyBarTop_exactAt (n : ℕ) : (dgHomologyBarComplex R F).ExactAt (n + 1) := by
  apply (HomologicalComplex.exactAt_iff' (K := dgHomologyBarComplex R F)
    (i := n + 2) (j := n + 1) (k := n) (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  exact dgHomologyBarTop_cycle_boundary R F n

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
