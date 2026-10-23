module

public import SerrePositivity.InfinityCategories.F2.CatPullbackConeLeg
public import SerrePositivity.InfinityCategories.F2.NativeConeTriangle
public import SerrePositivity.InfinityCategories.F1.Weighted.CosliceTransport

/-!
概要：Cat_∞ の引き戻し錐の実際の三角形と三辺の同定。
方針：元の cospan の辺上で native な錐の二単体を取り出す。
規約：二脚と底辺を元の指定関手の辺として厳密に保持する。
使われ方：native な可換関手同型と指定 path の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]

/-- 概要：元の cospan の射上の引き戻し錐の実際の二単体。
方針：join の錐の元の二単体を形状の指定辺で制限する。
規約：三角形の充填を新しく選択しない。
使われ方：native な錐の指定された二次の可換性。 -/
def catPullbackConeTriangle (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) : CatInfinity.{u} _⦋2⦌ :=
  nativeConeTriangle (catPullbackCone p q) (ULift.up (nerve.edgeMk f).edge)
/-- 概要：引き戻し錐の三角形の底辺は元の図式の射の辺。
方針：native な三角形の底辺と strict 図式の辺の式を使う。
規約：元の指定関手を保持する。
使われ方：三角形の三辺を実際の関手へ戻す。 -/
lemma catPullbackConeTriangle_zero (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    CatInfinity.δ 0 (catPullbackConeTriangle p q f) =
      (coherentNerveEdge ((catPullbackDiagram p q).map f)).edge := by
  rw [catPullbackConeTriangle, nativeConeTriangle_zero]
  exact strictCoherentDiagram_edge _ f
/-- 概要：引き戻し錐の三角形の長辺は終域の対象への読み戻した脚。
方針：形状の辺の終点と native な脚の回収の式を使う。
規約：元の一単体を変更しない。
使われ方：中心への脚を二辺の合成と比較する。 -/
lemma catPullbackConeTriangle_one (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    CatInfinity.δ 1 (catPullbackConeTriangle p q f) =
      (coherentNerveEdge (catPullbackConeFunctorLeg p q j)).edge := by
  let J := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan))
  have hk : J.δ 0 (ULift.up (nerve.edgeMk f).edge) = ULift.up (ComposableArrows.mk₀ j) := by
    apply ULift.ext
    exact (nerve.edgeMk f).tgt_eq
  have h := nativeConeTriangle_face (catPullbackCone p q)
    (ULift.up (nerve.edgeMk f).edge) (0 : Fin 2)
  exact h.trans ((congrArg (fun k : J _⦋0⦌ ↦ (nativeConeLeg (catPullbackCone p q) k).edge) hk).trans
    (catPullbackConeFunctorLeg_edge p q j).symm)
/-- 概要：引き戻し錐の三角形の最初の辺は始域の対象への読み戻した脚。
方針：形状の辺の始点と native な脚の回収の式を使う。
規約：元の一単体を変更しない。
使われ方：二射影と底辺の関手の合成を表す。 -/
lemma catPullbackConeTriangle_two (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    CatInfinity.δ 2 (catPullbackConeTriangle p q f) =
      (coherentNerveEdge (catPullbackConeFunctorLeg p q i)).edge := by
  let J := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan))
  have hk : J.δ 1 (ULift.up (nerve.edgeMk f).edge) = ULift.up (ComposableArrows.mk₀ i) := by
    apply ULift.ext
    exact (nerve.edgeMk f).src_eq
  have h := nativeConeTriangle_face (catPullbackCone p q)
    (ULift.up (nerve.edgeMk f).edge) (1 : Fin 2)
  exact h.trans ((congrArg (fun k : J _⦋0⦌ ↦ (nativeConeLeg (catPullbackCone p q) k).edge) hk).trans
    (catPullbackConeFunctorLeg_edge p q i).symm)

end SerrePositivity.InfinityCategories.F2
