module

public import SerrePositivity.InfinityCategories.HA.Monads.NativeMonad

/-!
概要：全モナド作用の単位を、全自己関手準圏の実際の辺として取り出す。
方針：Δ₊ の空順序集合から一点順序集合への射を全作用で写す。
規約：対象ごとの単位ではなくFun(C,C)内の辺。元の全作用の一部を取り出すだけである。
使われ方：HA §4.7.2–§4.7.3、Proposition 4.7.3.3 の元の単位の照合。
Riehl–Verity Definition 6.1.1、Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：walking monadの有限順序集合間の射を全Homの辺として表示する。
方針：nerveの指定辺を宇宙持ち上げする。
規約：始点・終点は元の順序集合の零単体。
使われ方：HA §4.7.2 の単位・積の全作用からの回収。 -/
def walkingMonadArrow {x y : AugmentedSimplexCategory} (f : x ⟶ y) :
    WalkingMonadShape.{u}.Edge (ULift.up (ComposableArrows.mk₀ x))
      (ULift.up (ComposableArrows.mk₀ y)) :=
  SSet.Edge.mk (ULift.up (ComposableArrows.mk₁ f))
    (congrArg ULift.up (CategoryTheory.nerve.edgeMk f).src_eq)
    (congrArg ULift.up (CategoryTheory.nerve.edgeMk f).tgt_eq)

namespace NativeMonad

variable {C : SSet.{u}}

/-- 概要：空順序集合の作用は同じ恒等自己関手の零単体。
方針：全単位の保存を零単体で評価する。
規約：curryと単位からの射による既存の頂点表示。
使われ方：HA Proposition 4.7.3.3 の元の単位の始点の照合。 -/
lemma unit_vertex (T : NativeMonad C) :
    T.action.app (Opposite.op ⦋0⦌)
      (ULift.up (ComposableArrows.mk₀ (WithInitial.star : AugmentedSimplexCategory))) =
        SSet.unitHomEquiv _ (curry' (𝟙 C)) := by
  have h := congrArg (fun f : 𝟙_ SSet ⟶ EndofunctorSpace C =>
    f.app (Opposite.op ⦋0⦌) PUnit.unit) T.map_unit
  change _ = (endofunctorUnit C).app (Opposite.op ⦋0⦌) PUnit.unit at h
  rw [endofunctorUnit_eq_curry] at h
  exact h

/-- 概要：全モナドの単位をFun(C,C)の実際の辺として回収する。
方針：空順序集合から一点順序集合への射を写し、両端の回収公式を使う。
規約：同じ恒等関手から同じunderlying endofunctorへの辺。
使われ方：HA Proposition 4.7.3.3 の指定単位の全自然性の検収。 -/
def unitEdge (T : NativeMonad C) :
    (EndofunctorSpace C).Edge (SSet.unitHomEquiv _ (curry' (𝟙 C)))
      (SSet.unitHomEquiv _ (curry' T.endofunctor)) := by
  let e := (walkingMonadArrow (WithInitial.homTo (⦋0⦌ : SimplexCategory))).map T.action
  exact SSet.Edge.mk e.edge (e.src_eq.trans T.unit_vertex)
    (e.tgt_eq.trans T.endofunctor_vertex.symm)

/-- 概要：回収した単位の辺の一次単体は元の全作用の同じ一次単体。
方針：辺の写像と端点の等式による輸送を展開する。
規約：h Funの類にする前の一次単体として比較する。
使われ方：HA Proposition 4.7.3.3 の元の全単位との比較。 -/
lemma unitEdge_edge (T : NativeMonad C) :
    T.unitEdge.edge = T.action.app (Opposite.op ⦋1⦌)
      (ULift.up (ComposableArrows.mk₁
        (WithInitial.homTo (⦋0⦌ : SimplexCategory)))) := rfl

end NativeMonad

end SerrePositivity.InfinityCategories.HA.Monads
