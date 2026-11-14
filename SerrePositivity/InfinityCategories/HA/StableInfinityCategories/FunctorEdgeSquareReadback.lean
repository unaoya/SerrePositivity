module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingSplitProjection
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：実比較正方形の対角辺を保ったまま、同じ cospan の普遍錐を構成する。
方針：端点で可逆なホモトピーによる矢印圏の同値と、厳密な錐の輸送を使う。
規約：一般安定性を仮定しない。使われ方：切除判定の第二条件と実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma squareTopArrow_functorEdge_vertex {X : SSet.{u}}
    {a b : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[1] : SSet.{u})).obj X)) a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareTopArrow (uncurry (SSet.yonedaEquiv.symm e.edge))).edge) = b := by
  erw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareTopArrow_edge, Equiv.symm_apply_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_uncurry_one e.edge).trans e.tgt_eq

lemma squareLeftArrow_functorEdge_edge {X : SSet.{u}}
    {a b : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[1] : SSet.{u})).obj X)) a b) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow (uncurry (SSet.yonedaEquiv.symm e.edge))).edge =
      (e.map ((truncation 2).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))).edge := by
  change e.edge.app (Opposite.op ⦋1⦌)
      (stdSimplex.objEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge).op
      ((Truncated.Edge.id (X := (truncation 2).obj (Δ[1] : SSet.{u}))
        (stdSimplex.obj₀Equiv.symm 0)).edge) =
    e.edge.app (Opposite.op ⦋1⦌) (𝟙 (Opposite.op ⦋1⦌))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) 1)
  have h : stdSimplex.objEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.{u}).edge = 𝟙 ⦋1⦌ := by
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    fin_cases i <;> rfl
  rw [h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
