module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarLowerCover

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits Opposite SSet AlgebraicTopology HomologicalComplex
open scoped Simplicial
variable (R : Type u) [CommRing R] {J : Type u} [PartialOrder J] [IsFiltered J]
  (F : J ⥤ ModuleCat.{u} R)

lemma dgHomologyBarFiltered_cycle_boundary (n : ℕ)
    (z : (dgHomologyBarComplex R F).X (n + 1))
    (hz : (dgHomologyBarComplex R F).d (n + 1) n z = 0) :
    ∃ a : (dgHomologyBarComplex R F).X (n + 2),
      (dgHomologyBarComplex R F).d (n + 2) (n + 1) a = z := by
  obtain ⟨b, a, ha⟩ := dgHomologyBarLowerMap_covers R F (n + 1) z
  have hz' : (dgHomologyBarComplex R (dgHomologyBarLowerDiagram R F b)).d (n + 1) n a = 0 := by
    apply dgHomologyBarLowerMap_injective R F b n
    rw [map_zero]
    have h := ConcreteCategory.congr_hom ((dgHomologyBarLowerMap R F b).comm (n + 1) n) a
    change (dgHomologyBarComplex R F).d (n + 1) n
      ((dgHomologyBarLowerMap R F b).f (n + 1) a) =
      (dgHomologyBarLowerMap R F b).f n
        ((dgHomologyBarComplex R (dgHomologyBarLowerDiagram R F b)).d (n + 1) n a) at h
    rw [ha, hz] at h
    exact h.symm
  obtain ⟨w, hw⟩ := dgHomologyBarTop_cycle_boundary R (dgHomologyBarLowerDiagram R F b) n a hz'
  refine ⟨(dgHomologyBarLowerMap R F b).f (n + 2) w, ?_⟩
  have h := ConcreteCategory.congr_hom ((dgHomologyBarLowerMap R F b).comm (n + 2) (n + 1)) w
  change (dgHomologyBarComplex R F).d (n + 2) (n + 1)
    ((dgHomologyBarLowerMap R F b).f (n + 2) w) =
    (dgHomologyBarLowerMap R F b).f (n + 1)
      ((dgHomologyBarComplex R (dgHomologyBarLowerDiagram R F b)).d (n + 2) (n + 1) w) at h
  exact h.trans ((congrArg ((dgHomologyBarLowerMap R F b).f (n + 1)) hw).trans ha)

lemma dgHomologyBarFiltered_exactAt (n : ℕ) : (dgHomologyBarComplex R F).ExactAt (n + 1) := by
  apply (HomologicalComplex.exactAt_iff' (K := dgHomologyBarComplex R F)
    (i := n + 2) (j := n + 1) (k := n) (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  exact dgHomologyBarFiltered_cycle_boundary R F n

end SerrePositivity.InfinityCategories
