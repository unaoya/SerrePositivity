module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ParametrizedSections
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation

/-!
概要：一点上の相対切断の族を、元の射影の同じ指定図式への引き戻しに同定する。
方針：既存の一点からの関手空間の評価同型を引き戻しの両成分に適用する。
規約：元のパラメータと元の値写像を厳密に保つ。
使われ方：under 圏の初頂点への制限と元の fibration の値の比較。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の一点上の切断の族は、元の評価図式に沿う同じ引き戻しと同型。 -/
def parametrizedSectionsPointIso {E Y P : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom (Δ[0] : SSet.{u})).obj Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSections p a ≅ pullback p (a ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso Y).hom) :=
  asIso (pullback.map ((ihom (Δ[0] : SSet.{u})).map p) a p
    (a ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso Y).hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).hom (𝟙 P)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso Y).hom rfl (by rw [Category.id_comp]))

/-- 同じ同型の元の値写像は一点での評価。 -/
lemma parametrizedSectionsPointIso_map {E Y P : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom (Δ[0] : SSet.{u})).obj Y) :
    (parametrizedSectionsPointIso p a).hom ≫ pullback.fst p _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsMap p a ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).hom := by
  exact pullback.lift_fst _ _ _

/-- 同じ同型は元のパラメータを厳密に保つ。 -/
lemma parametrizedSectionsPointIso_projection {E Y P : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom (Δ[0] : SSet.{u})).obj Y) :
    (parametrizedSectionsPointIso p a).hom ≫ pullback.snd p _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsProjection p a := by
  change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsProjection p a
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
