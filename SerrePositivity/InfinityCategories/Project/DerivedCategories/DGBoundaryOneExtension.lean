module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.EdgeHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-! # dg nerve の一次元境界の零辺による充填

概要：任意の二頂点を結ぶ零辺で一次元の境界写像を充填する。
方針：閉零元の端点付き辺と境界の面の外延性を使う。
規約：収縮元の仮定は不要。使われ方：β3 の始対象の低次元充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- dg nerve の任意の一次元境界写像は零辺で延長できる。 -/
lemma dgNerve_boundary_one_extension
    (b : (∂Δ[1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    ∃ F : (Δ[1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D, (∂Δ[1]).ι ≫ F = b := by
  let x : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 0 := SSet.yonedaEquiv (SSet.boundary.ι 1 ≫ b)
  let y : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 0 := SSet.yonedaEquiv (SSet.boundary.ι 0 ≫ b)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeOfCycle (A := A) (D := D) (x := x) (y := y) 0
  refine ⟨SSet.yonedaEquiv.symm e.edge, ?_⟩
  apply SSet.boundary.hom_ext
  intro j
  rw [← Category.assoc, SSet.boundary.ι_ι, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ j e.edge = SSet.yonedaEquiv (SSet.boundary.ι j ≫ b) := by
    fin_cases j
    · exact e.tgt_eq
    · exact e.src_eq
  rw [he, Equiv.symm_apply_apply]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
