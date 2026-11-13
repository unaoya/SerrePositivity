module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialOpposite
public import SerrePositivity.InfinityCategories.HA.Section6_1_1.SquareDuality
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceLeft

/-! # 安定性の自己双対性

概要：安定な quasicategory の反対も安定である。
方針：四角形を二座標の反転・交換で双対化し、零角と指定辺を保つ。
規約：安定性の定義の三条件を直接証明する。使われ方：二項積と双積の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：反対の単体集合の零頂点を元へ戻しても零頂点となる。
方針：始対象と終対象の反転の同値を使う。
規約：quasicategory 性は不要。使われ方：双対三角形の零角。 -/
lemma IsZeroVertex.unop {X : SSet.{u}} {x : X.op _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex x) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := X) (SSet.opObjEquiv x) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_iff_isTerminalVertex_op (SSet.opObjEquiv x)).2 hx.2,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_iff_isInitialVertex_op (SSet.opObjEquiv x)).2 hx.1⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroVertex (unop)


/-- 概要：零対象の存在は反対の単体集合へ移る。
方針：選んだ零頂点を反転する。
規約：quasicategory 性は不要。使われ方：反対圏の安定性の第一条件。 -/
instance hasZeroVertex_op {X : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X.op where
  exists_zero := by
    obtain ⟨z, hz⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex.exists_zero (X := X)
    exact ⟨SSet.opObjEquiv.symm z, hz.op⟩

/-- 概要：辺の反転を元へ戻してから単体を反転すると元の辺の表示となる。
方針：Yoneda で一次単体の反転とその逆を計算する。
規約：両端は辺の構造に保持する。使われ方：反対圏での fiber/cofiber の指定辺。 -/
lemma reverseSimplex_edgeUnop {X : SSet.{u}} {x y : X.op _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X.op) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex 1 (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edgeUnop (X := X) e).edge) =
      (SSet.yonedaEquiv (X := X.op) (n := ⦋1⦌)).symm e.edge := by
  let F : (Δ[1] : SSet.{u}) ⟶ X :=
    (SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).symm (SSet.opObjEquiv e.edge)
  have h : (SSet.yonedaEquiv (X := X.op) (n := ⦋1⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex 1 F) =
      SSet.opObjEquiv.symm ((SSet.yonedaEquiv (X := X) (n := ⦋1⦌)) F) := by
    change SSet.opObjEquiv.symm (F.app _ _) = SSet.opObjEquiv.symm (F.app _ _)
    congr 2
    apply stdSimplex.ext
    intro i
    change i.rev.rev = i
    exact Fin.rev_rev i
  apply (SSet.yonedaEquiv (X := X.op) (n := ⦋1⦌)).injective
  change (SSet.yonedaEquiv (X := X.op) (n := ⦋1⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex 1 F) = _
  rw [h]
  exact (congrArg SSet.opObjEquiv.symm
    ((SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).apply_symm_apply (SSet.opObjEquiv e.edge))).trans
      (((SSet.opObjEquiv (X := X)).symm_apply_apply e.edge).trans
        ((SSet.yonedaEquiv (X := X.op) (n := ⦋1⦌)).apply_symm_apply e.edge).symm)

/-- 概要：安定な quasicategory の反対も安定である。
方針：cofiber を双対化して fiber を作り、逆も同様に行う。
零角の列の同値は二重反転の値域同型を介して元の安定性へ帰着する。
規約：追加の有限極限・余極限の仮定は不要。使われ方：h C の二項積と双積。 -/
instance isStable_op {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X.op where
  toHasZeroVertex := inferInstance
  fiber_exists e := by
    let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edgeUnop (X := X) e)
    refine ⟨{
      square := _root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare s.square
      zero_corner := ?_
      right_edge := ?_
      isPullback := (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPushoutSquare_iff_dualSquare s.square).1 s.isPushout }⟩
    · rw [_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare_vertex]
      exact s.zero_corner.op
    · rw [_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare_rightEdge, s.bottom_edge]
      exact reverseSimplex_edgeUnop e
  cofiber_exists e := by
    let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenFiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edgeUnop (X := X) e)
    refine ⟨{
      square := _root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare s.square
      zero_corner := ?_
      bottom_edge := ?_
      isPushout := (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_dualSquare s.square).1 s.isPullback }⟩
    · rw [_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare_vertex]
      exact s.zero_corner.op
    · rw [_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare_bottomEdge, s.right_edge]
      exact reverseSimplex_edgeUnop e
  fiber_iff_cofiber t := by
    let q := (SSet.opFunctorCompOpFunctorIso.app X).hom
    let s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X :=
      { square := _root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare t.square ≫ q
        zero_corner := by
          change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := X) (SSet.opObjEquiv (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 1))
          exact t.zero_corner.unop }
    exact (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_dualSquare t.square).trans
      ((_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPushoutSquare_iff_postcomp_isIso (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare t.square) q).trans
        ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.fiber_iff_cofiber s).symm.trans
          ((_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_postcomp_isIso (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare t.square) q).symm.trans
            (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPushoutSquare_iff_dualSquare t.square).symm)))

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.1.1.13"] _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_op
