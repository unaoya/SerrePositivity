module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryPair

/-! # 両端を指定した辺の持ち上げ

概要：一次元境界の持ち上げ性から、指定された二頂点間の辺を持ち上げる。
方針：二頂点の境界図式を作り、持ち上げた一次単体の両端を計算する。
規約：quasicategory 性は仮定しない。
使われ方：S4 の普遍余錐間の比較射の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：一次元境界を持ち上げる射では任意の指定両端間の辺を持ち上げられる。
方針：境界図式を持ち上げ、Yoneda 表示により辺の端点と像を読む。
規約：元・値域は任意の単体集合。使われ方：普遍余錐の間の実際の辺。 -/
lemma exists_edge_lift_of_boundary_one {E B : SSet.{u}} (p : E ⟶ B)
    [HasLiftingProperty (boundary 1).ι p] (x y : E _⦋0⦌)
    (e : SSet.Truncated.Edge (X := (truncation 2).obj B)
      (p.app (Opposite.op ⦋0⦌) x) (p.app (Opposite.op ⦋0⦌) y)) :
    ∃ f : SSet.Truncated.Edge (X := (truncation 2).obj E) x y,
      f.map ((truncation 2).map p) = e := by
  have sq : CommSq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.stableBoundaryPair x y) (boundary 1).ι p
      (SSet.yonedaEquiv.symm e.edge) :=
    ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.stableBoundaryPair_postcomp x y p).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.stableBoundaryPair_edge e)⟩
  let L := sq.lift
  have hv₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex.{u} 0 0 ≫ (boundary 1).ι = stdSimplex.δ (1 : Fin 2) := by
    apply SSet.yonedaEquiv.injective
    decide
  have hv₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex.{u} 0 1 ≫ (boundary 1).ι = stdSimplex.δ (0 : Fin 2) := by
    apply SSet.yonedaEquiv.injective
    decide
  have h₀ : stdSimplex.δ (1 : Fin 2) ≫ L = SSet.yonedaEquiv.symm x := by
    rw [← hv₀, Category.assoc, sq.fac_left, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.stableBoundaryPair_zero]
  have h₁ : stdSimplex.δ (0 : Fin 2) ≫ L = SSet.yonedaEquiv.symm y := by
    rw [← hv₁, Category.assoc, sq.fac_left, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.stableBoundaryPair_one]
  let f : SSet.Truncated.Edge (X := (truncation 2).obj E) x y := {
    edge := SSet.yonedaEquiv L
    src_eq := by
      change E.δ 1 (SSet.yonedaEquiv L) = x
      rw [← stdSimplex.yonedaEquiv_δ_comp, h₀, Equiv.apply_symm_apply]
    tgt_eq := by
      change E.δ 0 (SSet.yonedaEquiv L) = y
      rw [← stdSimplex.yonedaEquiv_δ_comp, h₁, Equiv.apply_symm_apply] }
  refine ⟨f, SSet.Truncated.Edge.ext ?_⟩
  change p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv L) = e.edge
  rw [← SSet.yonedaEquiv_comp, sq.fac_right]
  exact SSet.yonedaEquiv.apply_symm_apply e.edge

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
