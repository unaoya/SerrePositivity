module

public import SerrePositivity.InfinityCategories.F2.Ind.ParametrizedSections
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation

/-!
概要：一点上の相対切断の族を、元の射影の同じ指定図式への引き戻しに同定する。
方針：既存の一点からの関手空間の評価同型を引き戻しの両成分に適用する。
規約：元のパラメータと元の値写像を厳密に保つ。
使われ方：under 圏の初頂点への制限と元の fibration の値の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の一点上の切断の族は、元の評価図式に沿う同じ引き戻しと同型。 -/
def parametrizedSectionsPointIso {E Y P : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom (Δ[0] : SSet.{u})).obj Y) :
    parametrizedSections p a ≅ pullback p (a ≫ (pointFunctorEvaluationIso Y).hom) :=
  asIso (pullback.map ((ihom (Δ[0] : SSet.{u})).map p) a p
    (a ≫ (pointFunctorEvaluationIso Y).hom) (pointFunctorEvaluationIso E).hom (𝟙 P)
    (pointFunctorEvaluationIso Y).hom rfl (by rw [Category.id_comp]))

/-- 同じ同型の元の値写像は一点での評価。 -/
lemma parametrizedSectionsPointIso_map {E Y P : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom (Δ[0] : SSet.{u})).obj Y) :
    (parametrizedSectionsPointIso p a).hom ≫ pullback.fst p _ =
      parametrizedSectionsMap p a ≫ (pointFunctorEvaluationIso E).hom := by
  exact pullback.lift_fst _ _ _

/-- 同じ同型は元のパラメータを厳密に保つ。 -/
lemma parametrizedSectionsPointIso_projection {E Y P : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom (Δ[0] : SSet.{u})).obj Y) :
    (parametrizedSectionsPointIso p a).hom ≫ pullback.snd p _ =
      parametrizedSectionsProjection p a := by
  change _ = parametrizedSectionsProjection p a
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

end SerrePositivity.InfinityCategories.F2.Ind
