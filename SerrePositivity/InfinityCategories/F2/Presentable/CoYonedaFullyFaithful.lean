module

public import SerrePositivity.InfinityCategories.F2.Presentable.TwistedOppositeHomComparison
public import SerrePositivity.InfinityCategories.F2.Compact.RepresentableRetractions
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityFullyFaithful
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorSpaceCurrying
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoYonedaConeLimits

/-!
概要：元の全 co-Yoneda 族と反対圏の Yoneda の全自然比較と充満忠実性。
方針：twisted Hom の両端交換を全二変数で分類し curry する。
規約：対象対ごとの同値だけから全関手の比較を推測しない。
使われ方：表現可能な全 Hom 極限から局所 Kan 余極限の存在へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Compact

/-- 概要：元の共変 Hom 変数の共同底を反対 Hom の共同底へ入れる。
方針：第一変数の二重反転を持ち上げ、積の宇宙比較を使う。
規約：元の両変数を保持する。
使われ方：全 co-Yoneda の uncurry の比較。 -/
def coYonedaOppositeJointBase (C : SSet.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj C ⊗
      (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶
        (SSet.uliftFunctor.{u + 1, u}).obj (C.op.op ⊗ C.op) :=
  ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctorCompOpFunctorIso.app C).inv ▷
    (SSet.uliftFunctor.{u + 1, u}).obj C.op) ≫ (uliftTensorIso C.op.op C.op).inv

/-- 概要：共同底の二つの交換を合成すると元の両変数の交換になる。
方針：全次数で同じ二つの射影を計算する。
規約：元の写像の厳密な等式である。
使われ方：co-Yoneda の元の共同評価の正規化。 -/
lemma coYonedaOppositeJointBase_swap (C : SSet.{u}) :
    coYonedaOppositeJointBase C ≫
      (SSet.uliftFunctor.{u + 1, u}).map (oppositeHomBaseIso C).hom =
      (β_ ((SSet.uliftFunctor.{u + 1, u}).obj C)
        ((SSet.uliftFunctor.{u + 1, u}).obj C.op)).hom ≫ (uliftTensorIso C.op C).inv := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 概要：元の全 co-Yoneda は反対圏の元の Yoneda と両変数で自然同型。
方針：全共同 Hom の両端交換の分類同型を curry する。
規約：元の全関手そのものを比較する。
使われ方：co-Yoneda の充満忠実性。 -/
def coyonedaInfinityMap_covariantRepresentableIso (C : SSet.{u}) [Quasicategory C] :
    FunctorIso (coyonedaInfinityMap C) (covariantRepresentableDiagram C) := by
  have e := (twistedOppositeHomInfinityIso C).precomp (coYonedaOppositeJointBase C)
  have hleft : coYonedaOppositeJointBase C ≫
      ((SSet.uliftFunctor.{u + 1, u}).map (oppositeHomBaseIso C).hom ≫
        twistedArrowHomInfinity C) = uncurry (coyonedaInfinityMap C) := by
    rw [← Category.assoc, coYonedaOppositeJointBase_swap, Category.assoc,
      coyonedaInfinityMap_uncurry]
    rfl
  have hright : coYonedaOppositeJointBase C ≫ twistedArrowHomInfinity C.op =
      uncurry (covariantRepresentableDiagram C) := by
    rw [covariantRepresentableDiagram, uncurry_pre_app, yonedaInfinityMap_uncurry]
    rfl
  rw [hleft, hright] at e
  have e' := e.curry
  simpa only [curry_uncurry] using e'

/-- 概要：元の全 co-Yoneda 写像は充満忠実。
方針：全自然同型で反対圏 Yoneda と同型な前合成同値へ移す。
規約：元の写像の実際の Hom 作用を判定する。
使われ方：co-Yoneda 像で得た表現可能な極限の持ち上げ。 -/
lemma coyonedaInfinityMap_isFullyFaithful (C : SSet.{u}) [Quasicategory C] :
    IsFullyFaithful (coyonedaInfinityMap C) := by
  have hpre := (isPrecompositionEquivalence_of_iso
    ((SSet.uliftFunctor.{u + 1, u}).mapIso (SSet.opFunctorCompOpFunctorIso.app C).symm)
    SpaceInfinity.{u}).isFullyFaithful
  have hcov : IsFullyFaithful (covariantRepresentableDiagram C) :=
    (yonedaInfinityMap_isFullyFaithful C.op).comp hpre
  exact (FunctorIso.isFullyFaithful_iff
    (coyonedaInfinityMap_covariantRepresentableIso C)).mpr hcov

end SerrePositivity.InfinityCategories.F2.Presentable
