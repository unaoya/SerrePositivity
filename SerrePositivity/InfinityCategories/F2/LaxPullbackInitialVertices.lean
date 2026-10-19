module

public import SerrePositivity.InfinityCategories.F2.PullbackInitialVertices
public import SerrePositivity.InfinityCategories.F2.TensorInitialVertices
public import SerrePositivity.InfinityCategories.F2.ArrowInitialVertices
public import SerrePositivity.InfinityCategories.F2.LaxPullbackMapping

/-!
概要：両入力とその像が始対象である lax pullback の頂点は始対象。
方針：矢印圏と両端の直積の始対象性を写像空間の引き戻し判定に渡す。
規約：頂点の元の指定矢印に追加条件を課さない。
使われ方：成分ごとの極限と零対象からの安定性への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：両入力とその像が始対象である lax pullback の頂点は始対象。
方針：両端評価の写像空間の Kan fibration 性と三成分の始対象性を使う。
規約：p と q の全ての極限の保存は仮定せず、指定頂点の像のみを要求する。
使われ方：零対象の構成と成分ごとの極限錐の普遍性。 -/
lemma isInitialVertex_laxPullback_of_components {A B C : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C]
    (p : A ⟶ C) (q : B ⟶ C) (x : (laxPullback p q) _⦋0⦌)
    (ha : IsInitialVertex ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) x))
    (hb : IsInitialVertex ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x))
    (hp : IsInitialVertex (p.app (Opposite.op ⦋0⦌)
      ((laxPullbackFst p q).app (Opposite.op ⦋0⦌) x)))
    (hq : IsInitialVertex (q.app (Opposite.op ⦋0⦌)
      ((laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x))) : IsInitialVertex x := by
  have : Quasicategory (A ⊗ B) := quasicategory_tensor A B
  have : Quasicategory (C ⊗ C) := quasicategory_tensor C C
  have h0 := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x) (laxPullbackArrow_source p q)
  have h1 := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x) (laxPullbackArrow_target p q)
  have he0 : IsInitialVertex
      ((evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)).app (Opposite.op ⦋0⦌)
        ((laxPullbackArrow p q).app (Opposite.op ⦋0⦌) x)) := h0.symm ▸ hp
  have he1 : IsInitialVertex
      ((evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1)).app (Opposite.op ⦋0⦌)
        ((laxPullbackArrow p q).app (Opposite.op ⦋0⦌) x)) := h1.symm ▸ hq
  apply isInitialVertex_pullback_of_components (arrowEndpointPair C) (p ⊗ₘ q)
    (fun _ _ ↦ inferInstance) x
  · exact isInitialVertex_arrow_of_endpoints _ he0 he1
  · exact isInitialVertex_tensor _ _ ha hb
  · exact isInitialVertex_tensor _ _ he0 he1

end SerrePositivity.InfinityCategories.F2
