module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.TwistedPairVertices

/-!
概要：元の左右の頂点と指定された単位から、同じ母対応の頂点を構成する。
方針：関手族を Yoneda で戻し、単位を定値図式として保持する。
規約：全関手圏の高次構成とは区別し、元の零単体を回収する。
使われ方：随伴対応の両射影の頂点上の本質的全射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：指定した両頂点と単位の零単体を同じ対応の頂点にする。
方針：twisted 零単体の射の一意性で、単位の終点の等式を図式全体へ戻す。
規約：新しい単位や関手を選ばない。
使われ方：元の随伴から対応の頂点を作る。 -/
def twistedPairLiftVertex {A B S T : SSet.{u}} (q : S ⟶ T) (b : A ⊗ B ⟶ T)
    (a : A _⦋0⦌) (r : B.op _⦋0⦌) (v : S _⦋0⦌)
    (h : q.app (Opposite.op ⦋0⦌) v = b.app (Opposite.op ⦋0⦌) (a, SSet.opObjEquiv r)) :
    twistedPairLift q b _⦋0⦌ where
  left := SSet.yonedaEquiv.symm a
  right := SSet.yonedaEquiv.symm r
  unit := SSet.const v
  condition := by
    apply twistedZeroMap_ext
    change q.app (Opposite.op ⦋0⦌) (PinchedHom.constant v 0) = _
    rw [pinchedConstant_zero]
    change q.app (Opposite.op ⦋0⦌) v =
      b.app (Opposite.op ⦋0⦌)
        ((SSet.yonedaEquiv.symm a).app (Opposite.op ⦋0⦌)
          ((edgewiseRight _).app (Opposite.op ⦋0⦌) twistedZeroPoint),
          (unopPairFamily (SSet.yonedaEquiv.symm r)).app (Opposite.op ⦋0⦌)
            ((edgewiseLeft _).app (Opposite.op ⦋0⦌) twistedZeroPoint))
    rw [unopPairFamily_vertex, Equiv.apply_symm_apply]
    have hz : (edgewiseRight (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌) twistedZeroPoint =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
      apply SSet.yonedaEquiv.symm.injective
      exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [hz]
    change q.app (Opposite.op ⦋0⦌) v = b.app (Opposite.op ⦋0⦌)
      (SSet.yonedaEquiv (SSet.yonedaEquiv.symm a), SSet.opObjEquiv r)
    rw [Equiv.apply_symm_apply]
    exact h

/-- 概要：構成した対応頂点の左射影は指定した元の左頂点。
方針：Yoneda の往復を使う。
規約：頂点の厳密な等式。
使われ方：左射影の全射性。 -/
lemma twistedPairLiftVertex_left {A B S T : SSet.{u}} (q : S ⟶ T) (b : A ⊗ B ⟶ T)
    (a : A _⦋0⦌) (r : B.op _⦋0⦌) (v : S _⦋0⦌)
    (h : q.app (Opposite.op ⦋0⦌) v = b.app (Opposite.op ⦋0⦌) (a, SSet.opObjEquiv r)) :
    (twistedPairLiftLeft q b).app (Opposite.op ⦋0⦌) (twistedPairLiftVertex q b a r v h) = a :=
  SSet.yonedaEquiv.apply_symm_apply a

/-- 概要：構成した対応頂点の右射影は指定した元の反対側の頂点。
方針：Yoneda の往復を使う。
規約：元の右頂点を反対圏の頂点として保持する。
使われ方：右射影の全射性。 -/
lemma twistedPairLiftVertex_right {A B S T : SSet.{u}} (q : S ⟶ T) (b : A ⊗ B ⟶ T)
    (a : A _⦋0⦌) (r : B.op _⦋0⦌) (v : S _⦋0⦌)
    (h : q.app (Opposite.op ⦋0⦌) v = b.app (Opposite.op ⦋0⦌) (a, SSet.opObjEquiv r)) :
    (twistedPairLiftRight q b).app (Opposite.op ⦋0⦌) (twistedPairLiftVertex q b a r v h) = r :=
  SSet.yonedaEquiv.apply_symm_apply r

/-- 概要：構成した対応頂点の単位は指定した元の零単体。
方針：同じ定値図式を零単体で評価する。
規約：単位を選び直さない。
使われ方：指定された随伴単位条件の回収。 -/
lemma twistedPairLiftVertex_unit {A B S T : SSet.{u}} (q : S ⟶ T) (b : A ⊗ B ⟶ T)
    (a : A _⦋0⦌) (r : B.op _⦋0⦌) (v : S _⦋0⦌)
    (h : q.app (Opposite.op ⦋0⦌) v = b.app (Opposite.op ⦋0⦌) (a, SSet.opObjEquiv r)) :
    twistedPairUnitVertex (twistedPairLiftVertex q b a r v h) = v := by
  exact pinchedConstant_zero v

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
