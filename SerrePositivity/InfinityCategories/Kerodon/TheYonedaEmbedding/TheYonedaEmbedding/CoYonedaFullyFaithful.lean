module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TwistedOppositeHomComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.RepresentableRetractions
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaInfinityFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorSpaceCurrying
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoYonedaConeLimits

/-!
概要：元の全 co-Yoneda 族と反対圏の Yoneda の全自然比較と充満忠実性。
方針：twisted Hom の両端交換を全二変数で分類し curry する。
規約：対象対ごとの同値だけから全関手の比較を推測しない。
使われ方：表現可能な全 Hom 極限から局所 Kan 余極限の存在へ戻す。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding


/-- 概要：元の共変 Hom 変数の共同底を反対 Hom の共同底へ入れる。
方針：第一変数の二重反転を持ち上げ、積の宇宙比較を使う。
規約：元の両変数を保持する。
使われ方：全 co-Yoneda の uncurry の比較。 -/
def coYonedaOppositeJointBase (C : SSet.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj C ⊗
      (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶
        (SSet.uliftFunctor.{u + 1, u}).obj (C.op.op ⊗ C.op) :=
  ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctorCompOpFunctorIso.app C).inv ▷
    (SSet.uliftFunctor.{u + 1, u}).obj C.op) ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso C.op.op C.op).inv

/-- 概要：共同底の二つの交換を合成すると元の両変数の交換になる。
方針：全次数で同じ二つの射影を計算する。
規約：元の写像の厳密な等式である。
使われ方：co-Yoneda の元の共同評価の正規化。 -/
lemma coYonedaOppositeJointBase_swap (C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coYonedaOppositeJointBase C ≫
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.oppositeHomBaseIso C).hom =
      (β_ ((SSet.uliftFunctor.{u + 1, u}).obj C)
        ((SSet.uliftFunctor.{u + 1, u}).obj C.op)).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso C.op C).inv := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 概要：元の全 co-Yoneda は反対圏の元の Yoneda と両変数で自然同型。
方針：全共同 Hom の両端交換の分類同型を curry する。
規約：元の全関手そのものを比較する。
使われ方：co-Yoneda の充満忠実性。 -/
def coyonedaInfinityMap_covariantRepresentableIso (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap C) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.covariantRepresentableDiagram C) := by
  have e := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedOppositeHomInfinityIso C).precomp (coYonedaOppositeJointBase C)
  have hleft : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coYonedaOppositeJointBase C ≫
      ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.oppositeHomBaseIso C).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C) = uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap C) := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coYonedaOppositeJointBase_swap, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap_uncurry]
    rfl
  have hright : coYonedaOppositeJointBase C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C.op =
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.covariantRepresentableDiagram C) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.covariantRepresentableDiagram, uncurry_pre_app, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_uncurry]
    rfl
  rw [hleft, hright] at e
  have e' := e.curry
  simpa only [curry_uncurry] using e'

/-- 概要：元の全 co-Yoneda 写像は充満忠実。
方針：全自然同型で反対圏 Yoneda と同型な前合成同値へ移す。
規約：元の写像の実際の Hom 作用を判定する。
使われ方：co-Yoneda 像で得た表現可能な極限の持ち上げ。 -/
lemma coyonedaInfinityMap_isFullyFaithful (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap C) := by
  have hpre := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    ((SSet.uliftFunctor.{u + 1, u}).mapIso (SSet.opFunctorCompOpFunctorIso.app C).symm)
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).isFullyFaithful
  have hcov : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.covariantRepresentableDiagram C) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_isFullyFaithful C.op).comp hpre
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.isFullyFaithful_iff
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coyonedaInfinityMap_covariantRepresentableIso C)).mpr hcov

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
