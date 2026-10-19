module

public import SerrePositivity.InfinityCategories.F2.EquivalenceHomotopyIsoPresentation
public import SerrePositivity.InfinityCategories.Core.EquivalencePathReplacement

/-!
概要：path 置換の指定ホモトピーと両端の回収。
方針：既存の path 成分を uncurry して端点を評価する。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {X Y : SSet.{u}}
/-- 概要：path 置換の指定ホモトピーと両端の回収。
方針：既存の path 成分を uncurry して端点を評価する。
規約：元の指定ホモトピーと同型を変更しない。
使われ方：native な錐の可換性と指定 path の最終整合。 -/
def replacementPathHomotopy (f : X ⟶ Y) :
    (Δ[1] : SSet.{u}) ⊗ equivalencePathReplacement f ⟶ Y :=
  uncurry (pullback.fst (equivalencePathEndpoint Y 0) f ≫ equivalencePathι Y)
/-- 概要：path 置換の指定ホモトピーと両端の回収。
方針：既存の path 成分を uncurry して端点を評価する。
規約：元の指定ホモトピーと同型を変更しない。
使われ方：native な錐の可換性と指定 path の最終整合。 -/
lemma replacementPathHomotopy_invertible (f : X ⟶ Y)
    (x : (equivalencePathReplacement f) _⦋0⦌) :
    IsInvertibleEdge (edgeOfSimplex ((replacementPathHomotopy f).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))) := by
  let a := pullback.fst (equivalencePathEndpoint Y 0) f
  have hx := fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) x)
  change IsEquivalencePathVertex ((a ≫ equivalencePathι Y).app (Opposite.op ⦋0⦌) x) at hx
  rw [← curry_uncurry (a ≫ equivalencePathι Y)] at hx
  unfold IsEquivalencePathVertex at hx
  rw [intervalFunctorVertexEdge_curry] at hx
  exact hx
/-- 概要：path 置換の指定ホモトピーと両端の回収。
方針：既存の path 成分を uncurry して端点を評価する。
規約：元の指定ホモトピーと同型を変更しない。
使われ方：native な錐の可換性と指定 path の最終整合。 -/
lemma replacementPathHomotopy_zero (f : X ⟶ Y) :
    prismEndpoint 0 (equivalencePathReplacement f) ≫ replacementPathHomotopy f =
      equivalencePathReplacementProjection f ≫ f := by
  rw [← curry_evaluateFunctorAt_interval, replacementPathHomotopy, curry_uncurry]
  exact pullback.condition (f := equivalencePathEndpoint Y 0) (g := f)
/-- 概要：path 置換の指定ホモトピーと両端の回収。
方針：既存の path 成分を uncurry して端点を評価する。
規約：元の指定ホモトピーと同型を変更しない。
使われ方：native な錐の可換性と指定 path の最終整合。 -/
lemma replacementPathHomotopy_one (f : X ⟶ Y) :
    prismEndpoint 1 (equivalencePathReplacement f) ≫ replacementPathHomotopy f =
      equivalencePathReplacementMap f := by
  rw [← curry_evaluateFunctorAt_interval, replacementPathHomotopy, curry_uncurry]
  rfl

end SerrePositivity.InfinityCategories.F2
