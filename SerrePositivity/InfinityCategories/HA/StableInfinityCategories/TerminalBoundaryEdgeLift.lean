module
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryPair
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeTerminalExtension

/-! # 指定した相対終対象への辺の持ち上げ

概要：相対終点境界充填により、指定した両端の間で基底の辺を持ち上げる。
方針：終点の条件を持つ一次元境界を作り、その境界を充填する。
規約：全ての終点に対する持ち上げ性は要求しない。
使われ方：S4 の TR3 の零頂点へ向かう辺の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：相対終点境界を充填する頂点への辺を、両端を指定して持ち上げられる。
方針：二頂点の境界を作り、指定した終点の相対充填を適用する。
規約：元・基底の quasicategory 性は不要。使われ方：終対象への列の比較。 -/
lemma exists_edge_lift_of_terminalBoundaryLifting {E B : SSet.{u}} (p : E ⟶ B)
    (x y : E _⦋0⦌) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p y)
    (e : SSet.Truncated.Edge (X := (truncation 2).obj B)
      (p.app (Opposite.op ⦋0⦌) x) (p.app (Opposite.op ⦋0⦌) y)) :
    ∃ f : SSet.Truncated.Edge (X := (truncation 2).obj E) x y,
      f.map ((truncation 2).map p) = e := by
  have sq : CommSq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.stableBoundaryPair x y) (boundary 1).ι p
      (SSet.yonedaEquiv.symm e.edge) :=
    ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.stableBoundaryPair_postcomp x y p).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.stableBoundaryPair_edge e)⟩
  obtain ⟨L, hL, hLp⟩ := ht 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.stableBoundaryPair x y) (SSet.yonedaEquiv.symm e.edge)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.stableBoundaryPair_one x y) sq
  have hv₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex.{u} 0 0 ≫ (boundary 1).ι = stdSimplex.δ (1 : Fin 2) := by
    apply SSet.yonedaEquiv.injective
    decide
  have hv₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex.{u} 0 1 ≫ (boundary 1).ι = stdSimplex.δ (0 : Fin 2) := by
    apply SSet.yonedaEquiv.injective
    decide
  have h₀ : stdSimplex.δ (1 : Fin 2) ≫ L = SSet.yonedaEquiv.symm x := by
    rw [← hv₀, Category.assoc, hL, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.stableBoundaryPair_zero]
  have h₁ : stdSimplex.δ (0 : Fin 2) ≫ L = SSet.yonedaEquiv.symm y := by
    rw [← hv₁, Category.assoc, hL, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.stableBoundaryPair_one]
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
  rw [← SSet.yonedaEquiv_comp, hLp]
  exact SSet.yonedaEquiv.apply_symm_apply e.edge

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
