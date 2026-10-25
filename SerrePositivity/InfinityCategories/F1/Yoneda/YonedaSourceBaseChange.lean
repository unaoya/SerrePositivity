module

public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.Source
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningBaseChange

/-!
概要：元の Yoneda 写像の第一変数での評価を、始点固定の twisted arrow の分類へ照合する。
方針：元の共同 Hom 評価の第一変数を固定し、同じ射影の底変換同型を使う。
規約：元の Yoneda 全射を保つ新規の葉。既存の深層モジュールは変更しない。
使われ方：Yoneda による元の極限錐の保存と Ind の有限極限の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の Yoneda 全射の評価は、同じ第一変数固定の底の包含による共同評価の制限。 -/
lemma yonedaInfinityMap_evaluation_eq_sourceRestriction {C : SSet.{u}} [Quasicategory C]
    (x : C _⦋0⦌) :
    yonedaInfinityMap C ≫ presheafInfinityEvaluation x =
      (SSet.uliftFunctor.{u + 1, u}).map (twistedArrowSourceInclusion x) ≫
        twistedArrowHomInfinity C := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro y
  change (homInfinityJointEvaluation C).app n
    (PinchedHom.constant (ULift.up (SSet.opObjEquiv.symm x)) n.unop.len,
      (SSet.uliftFunctor.{u + 1, u}.obj C).map (𝟙 n) y) = _
  rw [Functor.map_id_apply]
  rfl

/-- 評価した元の Yoneda 図式は、始点固定の同じ全空間の分類図式と全関手同型。 -/
def yonedaInfinityMap_evaluation_sourceIso {C : SSet.{u}} [Quasicategory C]
    (x : C _⦋0⦌) :
    FunctorIso (yonedaInfinityMap C ≫ presheafInfinityEvaluation x)
      (leftStraighteningInfinityDiagram (twistedArrowSourceProjection x)) := by
  rw [yonedaInfinityMap_evaluation_eq_sourceRestriction]
  exact leftStraighteningInfinityDiagram_baseChangeIso
    (twistedArrowProjection C) (twistedArrowSourceInclusion x)

end SerrePositivity.InfinityCategories
