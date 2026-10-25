module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairUnitPointedRestrictions
public import SerrePositivity.InfinityCategories.F1.Fibrations.VertexFiberTotalIso

/-!
概要：左右の固定単位の同じ pointed 比較の実際の fiber 作用は同値。
方針：固定単位の引き戻しの fiber 同型を持ち上げ、同じ全体の分類 fiber 比較へ続ける。
規約：元の全空間比較の作用をそのまま照合する。
使われ方：始単位での相対評価と元の全左 Hom の輸送の同じ指定点を保つ比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：固定左の fiber を同じ全二変数単位空間の fiber へ厳密に移す。
方針：底上の全空間同型と元の引き戻しの fiber 同型を合成する。
規約：同じ固定左包含の作用を保持する。
使われ方：固定左の pointed 比較の同値性。 -/
def pairLeftUnitJointFiberIso {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌) :
    vertexFiber (preservingLeftUnitProjection v) w ≅
      vertexFiber (covariantPairUnitProjection C D)
        ((pairFixedLeftBase v).app (Opposite.op ⦋0⦌) w) :=
  vertexFiberTotalIso (preservingLeftUnitProjection v)
    (pullback.snd (covariantPairUnitProjection C D) (pairFixedLeftBase v))
    (pairFixedLeftCosliceIso v).symm
    ((Iso.inv_comp_eq (pairFixedLeftCosliceIso v)).mpr
      (pairFixedLeftCosliceIso_projection v).symm) w ≪≫
    vertexFiberPullbackIso (covariantPairUnitProjection C D) (pairFixedLeftBase v) w

/-- 概要：固定左の fiber 同型は元の全単位空間への包含を保持する。
方針：二つの元の fiber 同型の包含の公式を使う。
規約：元の実単位の全単体を保持する。
使われ方：同じ pointed 比較の直接の作用の同定。 -/
lemma pairLeftUnitJointFiberIso_ι {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌) :
    (pairLeftUnitJointFiberIso v w).hom ≫ vertexFiberι (covariantPairUnitProjection C D)
        ((pairFixedLeftBase v).app (Opposite.op ⦋0⦌) w) =
      vertexFiberι (preservingLeftUnitProjection v) w ≫ pairLeftUnitIntoJoint v := by
  simp only [pairLeftUnitJointFiberIso, Iso.trans_hom, Category.assoc,
    vertexFiberPullbackIso_hom_ι, vertexFiberTotalIso]
  rw [← Category.assoc, vertexFiberMap_ι, Category.assoc]
  rfl

/-- 概要：元の固定左 fiber 同型の持ち上げを同じ大きい fiber の同型にする。
方針：元の厳密な同型の宇宙持ち上げを両端の標準 fiber 同型で挟む。
規約：同じ実単位の像を使う。
使われ方：pointed-space への全体の分類比較との接続。 -/
def pairLeftUnitLiftedJointFiberIso {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌) :
    vertexFiber ((SSet.uliftFunctor.{u + 2, u + 1}).map (preservingLeftUnitProjection v))
        (ULift.up w) ≅
      vertexFiber ((SSet.uliftFunctor.{u + 2, u + 1}).map (covariantPairUnitProjection C D))
        (ULift.up ((pairFixedLeftBase v).app (Opposite.op ⦋0⦌) w)) :=
  (uliftVertexFiberIso.{u + 1, u + 2} (preservingLeftUnitProjection v) w).symm ≪≫
    (SSet.uliftFunctor.{u + 2, u + 1}).mapIso (pairLeftUnitJointFiberIso v w) ≪≫
    uliftVertexFiberIso.{u + 1, u + 2} (covariantPairUnitProjection C D)
      ((pairFixedLeftBase v).app (Opposite.op ⦋0⦌) w)

/-- 概要：同じ持ち上げた固定左 fiber 同型は元の包含を厳密に保つ。
方針：標準 fiber 持ち上げ同型と元の固定左包含の公式を使う。
規約：元の全空間の射と可換。
使われ方：固定左の pointed 比較の実 fiber 射の照合。 -/
lemma pairLeftUnitLiftedJointFiberIso_ι {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌) :
    (pairLeftUnitLiftedJointFiberIso v w).hom ≫
      vertexFiberι ((SSet.uliftFunctor.{u + 2, u + 1}).map (covariantPairUnitProjection C D))
        (ULift.up ((pairFixedLeftBase v).app (Opposite.op ⦋0⦌) w)) =
      vertexFiberι ((SSet.uliftFunctor.{u + 2, u + 1}).map (preservingLeftUnitProjection v))
        (ULift.up w) ≫ (SSet.uliftFunctor.{u + 2, u + 1}).map (pairLeftUnitIntoJoint v) := by
  dsimp only [pairLeftUnitLiftedJointFiberIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [uliftVertexFiberIso_hom_ι, ← CategoryTheory.Functor.map_comp,
    pairLeftUnitJointFiberIso_ι, CategoryTheory.Functor.map_comp]
  have h := congrArg (fun f ↦ f ≫
    (SSet.uliftFunctor.{u + 2, u + 1}).map (pairLeftUnitIntoJoint v))
    (uliftVertexFiberIso_inv_ι.{u + 1, u + 2} (preservingLeftUnitProjection v) w)
  simpa only [Category.assoc] using h

/-- 概要：固定左の同じ pointed 比較の実 fiber 射。
方針：元の可換正方形の fiber 写像を取る。
規約：同じ元の全関手の固定値の上にある。
使われ方：相対評価の始単位の pointed 像。 -/
def pairLeftUnitPointedDisplayFiber {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌) :=
  transportSquareFiberMap
    ((SSet.uliftFunctor.{u + 2, u + 1}).map (preservingLeftUnitProjection v))
    pointedSpaceProjection (pairLeftUnitPointedDisplay v) (pairUnitHomAtLeft v)
    (pairLeftUnitPointedDisplay_projection v) (ULift.up w)

/-- 概要：固定左の実 fiber 射は元の全体の fiber 比較と同じ射。
方針：同じ全空間への包含後に持ち上げた fiber 同型の公式を使う。
規約：元の pointed 比較の作用を置き換えない。
使われ方：固定左の同値性。 -/
lemma pairLeftUnitPointedDisplayFiber_compare {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌) :
    pairLeftUnitPointedDisplayFiber v w =
      (pairLeftUnitLiftedJointFiberIso v w).hom ≫
        pairClassifierPointedDisplayFiber (covariantPairUnitProjection C D)
          ((pairFixedLeftBase v).app (Opposite.op ⦋0⦌) w) := by
  apply vertexFiber_hom_ext pointedSpaceProjection
    ((pairUnitHomAtLeft v).app (Opposite.op ⦋0⦌) (ULift.up w))
  let p := (SSet.uliftFunctor.{u + 2, u + 1}).map (preservingLeftUnitProjection v)
  let q := (SSet.uliftFunctor.{u + 2, u + 1}).map (covariantPairUnitProjection C D)
  let z := ULift.up ((pairFixedLeftBase v).app (Opposite.op ⦋0⦌) w)
  let t := (pairUnitHomAtLeft v).app (Opposite.op ⦋0⦌) (ULift.up w)
  let e := pairLeftUnitLiftedJointFiberIso v w
  let k := pairClassifierPointedDisplayFiber (covariantPairUnitProjection C D)
    ((pairFixedLeftBase v).app (Opposite.op ⦋0⦌) w)
  have hk : k ≫ vertexFiberι pointedSpaceProjection t =
      vertexFiberι q z ≫ pairUnitPointedDisplay C D :=
    transportSquareFiberMap_ι q pointedSpaceProjection (pairUnitPointedDisplay C D)
      (pairUnitHomBifunctor C D) (pairUnitPointedDisplay_projection C D) z
  calc
    pairLeftUnitPointedDisplayFiber v w ≫ vertexFiberι pointedSpaceProjection t =
        vertexFiberι p (ULift.up w) ≫ pairLeftUnitPointedDisplay v :=
      transportSquareFiberMap_ι p pointedSpaceProjection (pairLeftUnitPointedDisplay v)
        (pairUnitHomAtLeft v) (pairLeftUnitPointedDisplay_projection v) (ULift.up w)
    _ = (vertexFiberι p (ULift.up w) ≫
          (SSet.uliftFunctor.{u + 2, u + 1}).map (pairLeftUnitIntoJoint v)) ≫
            pairUnitPointedDisplay C D := (Category.assoc _ _ _).symm
    _ = (e.hom ≫ vertexFiberι q z) ≫ pairUnitPointedDisplay C D :=
      congrArg (· ≫ pairUnitPointedDisplay C D) (pairLeftUnitLiftedJointFiberIso_ι v w).symm
    _ = e.hom ≫ (k ≫ vertexFiberι pointedSpaceProjection t) :=
      (Category.assoc _ _ _).trans (congrArg (e.hom ≫ ·) hk.symm)
    _ = (e.hom ≫ k) ≫ vertexFiberι pointedSpaceProjection t := (Category.assoc _ _ _).symm

/-- 概要：固定左の元の pointed 比較の実 fiber 作用は同値。
方針：厳密な固定左 fiber 同型と同じ全体の fiber 同値を合成する。
規約：元の作用に対する結論。
使われ方：実単位を保つ全相対評価の比較。 -/
lemma pairLeftUnitPointedDisplayFiber_isQCatEquivalence {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌) :
    IsQCatEquivalence (pairLeftUnitPointedDisplayFiber v w) := by
  rw [pairLeftUnitPointedDisplayFiber_compare]
  exact (qCatEquivalenceOfIso (pairLeftUnitLiftedJointFiberIso v w)).isQCatEquivalence.comp
    (pairClassifierPointedDisplayFiber_isQCatEquivalence _ _)

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
