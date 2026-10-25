module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairUnitHomRestriction

/-!
概要：両変数に自然な全単位族を、元の一つの右関手に制限する。
方針：同じ二変数族に右固定の底の射を前合成する。
規約：元の全左関手圏と全自然変換を保持する。
使われ方：固定右の普遍単位による表現可能性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：元の右関手を固定して左関手を全体で動かす底の射。
方針：左側の恒等写像と元の右頂点の定値写像を組にする。
規約：元の全左関手圏を始域にする。
使われ方：同じ全単位族の右固定制限。 -/
def pairFixedRightBase {C D : PresentableInfinityObject.{u}}
    (w : PrRFunctorSpace D C _⦋0⦌) :
    PrLFunctorSpace C D ⟶ PrLFunctorSpace C D ⊗ PrRFunctorSpace D C :=
  lift (𝟙 _) (SSet.const w)

/-- 概要：固定右での元の二変数合成は、その右関手による後合成。
方針：元の全部分関手圏の包含と固定右の内部 Hom の公式を使う。
規約：全左関手の自然変換を保持する。
使われ方：固定右 coslice と分類図式の接続。 -/
lemma pairFixedRightBase_composition {C D : PresentableInfinityObject.{u}}
    (w : PrRFunctorSpace D C _⦋0⦌) :
    pairFixedRightBase w ≫ pairUnitComposition C D =
      leftFunctorInclusion C D ≫ (ihom C.obj).map (rightVertexFunctor w) := by
  have hw : (rightFunctorInclusion D C).app (Opposite.op ⦋0⦌) w =
      functorVertex (rightVertexFunctor w) :=
    ((functorVertexEquiv D.obj C.obj).apply_symm_apply w.val).symm
  unfold pairFixedRightBase pairUnitComposition
  rw [← Category.assoc, lift_map, SSet.const_comp, Category.id_comp, hw]
  rw [← internalHomComposition_fixedRight (A := C.obj) (rightVertexFunctor w),
    ← Category.assoc, comp_lift, SSet.comp_const, Category.comp_id]

/-- 概要：元の右関手に制限した実単位空間の同じ分類図式。
方針：全二変数族に右固定の底の射の宇宙持ち上げを前合成する。
規約：元の分類関手を選び直さない。
使われ方：全左関手圏上の固定右の表現可能性。 -/
def pairUnitHomAtRight {C D : PresentableInfinityObject.{u}}
    (w : PrRFunctorSpace D C _⦋0⦌) :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj (PrLFunctorSpace C D) ⟶ SpaceInfinity.{u + 1} :=
  (SSet.uliftFunctor.{u + 2, u + 1}).map (pairFixedRightBase w) ≫ pairUnitHomBifunctor C D

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
