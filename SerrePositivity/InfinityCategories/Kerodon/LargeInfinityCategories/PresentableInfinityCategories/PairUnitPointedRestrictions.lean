module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairClassifierPointedDisplay
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairUnitRelativeEvaluation

/-!
概要：元の全単位空間の pointed-space 比較を固定左・固定右の実単位へ制限する。
方針：元の引き戻し同型の逆を同じ全空間比較に前合成する。
規約：両側に同じ実単位を同じ一つの比較で送る。
使われ方：単位での相対評価と元の全関手の Hom 作用の照合。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

instance pairFunctorProduct_quasicategory (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C) :=
  quasicategory_of_innerFibration (fst (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C))

/-- 概要：元の全実単位空間を同じ分類図式上の pointed-space へ送る。
方針：構成済みの同じ left fibration の全空間比較を使う。
規約：元の左右の全関手族を保持する。
使われ方：左右の単位点を同じ分類の値へ移す。 -/
def pairUnitPointedDisplay (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CovariantPairUnitSpace C D) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairClassifierPointedDisplay (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantPairUnitProjection C D)

/-- 概要：全実単位の pointed 比較は元の同じ分類図式の上にある。
方針：元の分類正方形の可換性を適用する。
規約：底の元の二変数族を変えない。
使われ方：指定単位での輸送自然性。 -/
lemma pairUnitPointedDisplay_projection (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    pairUnitPointedDisplay C D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantPairUnitProjection C D) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairUnitHomBifunctor C D := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairClassifierPointedDisplay_projection _

/-- 概要：固定左の元の単位空間を全二変数単位空間に含める。
方針：固定左の厳密な引き戻し同型の逆の後に第一脚を続ける。
規約：元の実単位を選び直さない。
使われ方：固定左の pointed 比較。 -/
def pairLeftUnitIntoJoint {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservingLeftUnitCoslice v ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CovariantPairUnitSpace C D :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedLeftCosliceIso v).inv ≫
    pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantPairUnitProjection C D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedLeftBase v)

/-- 概要：固定左の全空間包含は元の右関手の底を保持する。
方針：同じ引き戻し同型の第二脚の公式を逆向きに使う。
規約：元の全右関手圏からの底の射。
使われ方：単位輸送の可換正方形。 -/
lemma pairLeftUnitIntoJoint_projection {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) :
    pairLeftUnitIntoJoint v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantPairUnitProjection C D =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservingLeftUnitProjection v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedLeftBase v := by
  have h : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedLeftCosliceIso v).inv ≫
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantPairUnitProjection C D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedLeftBase v) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservingLeftUnitProjection v :=
    (Iso.inv_comp_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedLeftCosliceIso v)).mpr
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedLeftCosliceIso_projection v).symm
  rw [pairLeftUnitIntoJoint, Category.assoc, pullback.condition, ← Category.assoc, h]

/-- 概要：固定右の元の単位空間を全二変数単位空間に含める。
方針：固定右の同じ引き戻し同型の逆を第一脚へ続ける。
規約：同じ実単位を全二変数空間に送る。
使われ方：固定右の pointed 比較。 -/
def pairRightUnitIntoJoint {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservingRightUnitCoslice w ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CovariantPairUnitSpace C D :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedRightCosliceIso w).inv ≫
    pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantPairUnitProjection C D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedRightBase w)

/-- 概要：固定右の全空間包含は元の左関手の底を保持する。
方針：同じ引き戻し同型の第二脚の公式を逆向きに使う。
規約：元の全左関手圏からの底の射。
使われ方：指定単位での輸送の自然性。 -/
lemma pairRightUnitIntoJoint_projection {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) :
    pairRightUnitIntoJoint w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantPairUnitProjection C D =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservingRightUnitProjection w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedRightBase w := by
  have h : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedRightCosliceIso w).inv ≫
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantPairUnitProjection C D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedRightBase w) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservingRightUnitProjection w :=
    (Iso.inv_comp_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedRightCosliceIso w)).mpr
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairFixedRightCosliceIso_projection w).symm
  rw [pairRightUnitIntoJoint, Category.assoc, pullback.condition, ← Category.assoc, h]

/-- 概要：固定左単位空間の同じ pointed 比較。
方針：元の全空間包含の宇宙持ち上げを全体の比較に前合成する。
規約：同じ単位の像を使う。
使われ方：相対関手評価の指定点。 -/
def pairLeftUnitPointedDisplay {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservingLeftUnitCoslice v) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u + 1} :=
  (SSet.uliftFunctor.{u + 2, u + 1}).map (pairLeftUnitIntoJoint v) ≫ pairUnitPointedDisplay C D

/-- 概要：固定左の pointed 比較の底は元の全単位族の同じ固定左値。
方針：同じ全空間包含の可換性を分類正方形に続ける。
規約：分類の値を別に選ばない。
使われ方：元の関手族の Hom 作用との比較。 -/
lemma pairLeftUnitPointedDisplay_projection {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) :
    pairLeftUnitPointedDisplay v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservingLeftUnitProjection v) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairUnitHomAtLeft v := by
  rw [pairLeftUnitPointedDisplay, Category.assoc, pairUnitPointedDisplay_projection,
    ← CategoryTheory.Functor.map_comp_assoc, pairLeftUnitIntoJoint_projection,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

/-- 概要：固定右単位空間の同じ pointed 比較。
方針：元の固定右包含の持ち上げを同じ全体比較へ続ける。
規約：左右の評価に同じ実単位の像を使う。
使われ方：元の左 Hom に沿う単位輸送。 -/
def pairRightUnitPointedDisplay {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservingRightUnitCoslice w) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u + 1} :=
  (SSet.uliftFunctor.{u + 2, u + 1}).map (pairRightUnitIntoJoint w) ≫ pairUnitPointedDisplay C D

/-- 概要：固定右の pointed 比較の底は元の全二変数族の同じ固定右値。
方針：同じ右固定包含の可換性を全体の分類正方形に続ける。
規約：元の全左関手族を保持する。
使われ方：同じ単位での輸送の同値性。 -/
lemma pairRightUnitPointedDisplay_projection {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) :
    pairRightUnitPointedDisplay w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservingRightUnitProjection w) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairUnitHomAtRight w := by
  rw [pairRightUnitPointedDisplay, Category.assoc, pairUnitPointedDisplay_projection,
    ← CategoryTheory.Functor.map_comp_assoc, pairRightUnitIntoJoint_projection,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
